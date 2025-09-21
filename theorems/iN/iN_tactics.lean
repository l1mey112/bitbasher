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

syntax "iN_convert_goal_bitvec" : tactic
macro_rules
  | `(tactic| iN_convert_goal_bitvec) => `(tactic|
    first
    | fail_if_success (intro (v : iN (_)))
    | intro (v : iN (_))
      cases v
      case poison =>
        simp [simp_iN]

      simp [simp_iN]
      iN_convert_goal_bitvec
      (try revert x)
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
      revert_iN
      iN_convert_goal_bitvec
      -- there might be no more goals after this
      all_goals solve
        | grind
        -- `blast_bv` wouldn't be able to solve ∀n bitwidth goals. give up here
        | bv_normalize
    )
  )
  | `(tactic| blast $tac) => `(tactic|
    (
      revert_iN
      iN_convert_goal_bitvec
      -- there might be no more goals after this
      all_goals solve
        | grind
        | cases $tac <;> grind
        | cases $tac
          blast_bv
    )
  )
