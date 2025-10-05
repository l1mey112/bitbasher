import Lean
import theorems.iN.iN_def
import theorems.iN.iN_rewrite
import theorems.iN.iN_lemmas
import theorems.iN.SimpSets

open Lean Elab Tactic Meta Simp

def revertiN (g : MVarId) : MetaM (Array FVarId × MVarId) := do
  let type ← g.getType
  let (_, fvars) ← type.forEachWhere Expr.isFVar collector |>.run {}
  g.revert fvars.toArray
where
  collector (e : Expr) : StateT (Std.HashSet FVarId) MetaM Unit := do
    let fvarId := e.fvarId!
    let typ ← fvarId.getType
    match_expr typ with
    | iN _ =>
      modify fun s => s.insert fvarId
    | _ => return ()

elab "revert_iN" : tactic => do
  let g ← getMainGoal
  let (_, g') ← revertiN g
  replaceMainGoal [g']

-- Tactic inspired by Lean MLIR in `SSA/Projects/InstCombine/Tactic/SimpLLVM.lean`

syntax "iN_convert_goal_bitvec'" : tactic
macro_rules
  | `(tactic| iN_convert_goal_bitvec') => `(tactic|
    first
    | fail_if_success (intro (v : iN (_)))
    | intro (v : iN (_))

      cases v
      case poison =>
        simp [simp_iN]

      iN_convert_goal_bitvec'
      (try revert x)
    )

syntax "iN_convert_goal_bitvec" : tactic
macro_rules
  | `(tactic| iN_convert_goal_bitvec) => `(tactic|
    revert_iN;
    iN_convert_goal_bitvec'
  )

syntax "blast_bv" : tactic
macro_rules
  | `(tactic| blast_bv) => `(tactic|
    (
      repeat(
        all_goals try simp_all
        any_goals split
      )
      all_goals
        solve
        | bv_decide +acNf
    )
  )

syntax "blast" : tactic
syntax "blast" Lean.Parser.Tactic.elimTarget : tactic

macro_rules
  | `(tactic| blast) => `(tactic|
    (
      iN_convert_goal_bitvec
      simp [simp_iN]
      -- there might be no more goals after this
      all_goals solve
        | grind
        -- `blast_bv` wouldn't be able to solve ∀n bitwidth goals. give up here
        | bv_normalize
    )
  )
  | `(tactic| blast $tac) => `(tactic|
    (
      iN_convert_goal_bitvec
      simp [simp_iN]
      -- there might be no more goals after this
      all_goals solve
        | grind
        | cases $tac <;> grind
        | cases $tac
          blast_bv
    )
  )

/-- `poison_unroll x y z => a b c`

Performs `cases x; cases y; cases z`, solves every `poison` branch with
`simp [iN_unwrap_inst]`, and in the unique `bitvec` branch introduces the
payloads named `a b c`. -/
syntax "poison_unroll" (ppSpace colGt ident)* " =>" (ppSpace colGt ident)* : tactic
macro_rules
| `(tactic| poison_unroll $xs:ident* => $ys:ident*) =>
  `(tactic|
    ($[cases $xs:ident with
      | bitvec $ys:ident => ?_
      | poison => simp [simp_iN]];*))
