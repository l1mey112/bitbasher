import Lean
import theorems.iN.iN_def

open Lean Elab Tactic Meta Simp

-- https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Clearing.20obvious.20contradictions.20in.20cases.20of.20goals/near/538579820

/- elab "unfold_to_bitvec" : tactic => do
  withMainContext do
    evalTactic (← `(tactic| simp [iN_unwrap_inst])) -/

/- theorem and_false_eq {p : Prop} (q : Prop) (h : p = False) : (p ∧ q) = False := by simp [*]

open Lean Meta Simp
simproc ↓ shortCircuitAnd (And _ _) := fun e => do
  let_expr And p q := e | return .continue
  let r ← simp p
  let_expr False := r.expr | return .continue
  let proof ← mkAppM ``and_false_eq #[q, (← r.getProof)]
  return .done { expr := r.expr, proof? := some proof } -/

/- simproc ↓ bifBitvec (cond _ (bitvec _) (bitvec _)) := fun e => do
  let_expr cond v lhs rhs := e | return .continue
  unless ← matchesInstance lhs (mkConst ``bitvec) do return .continue
  unless ← matchesInstance rhs (mkConst ``bitvec) do return .continue

  let a := lhs.getArg! 0
  let b := rhs.getArg! 0

  let an := rhs.getArg! 1

  --let some va ← getBitVecValue? (lhs.getArg! 0) | return .continue
  --let some vb ← getBitVecValue? (rhs.getArg! 0) | return .continue

  -- va : (n : Nat) × BitVec n
  -- vb : (n : Nat) × BitVec n

  let expr := mkApp2 (mkConst ``iN.bitvec) (an) (mkApp3 (mkConst ``ite) v a b)
  return .done { expr := expr, proof? := none } -/

/- /-- `poison_unroll x y z => a b c`

Performs `cases x; cases y; cases z`, solves every `poison` branch with
`simp [iN_unwrap_inst]`, and in the unique `bitvec` branch introduces the
payloads named `a b c`. -/
syntax "poison_unroll" (ppSpace colGt ident)* " =>" (ppSpace colGt ident)* : tactic
macro_rules
| `(tactic| poison_unroll $xs:ident* => $ys:ident*) => do

  unless xs.size == ys.size do
    Macro.throwError s!"poison_unroll: got {xs.size} variables but {ys.size} names"

  let rec go (i : Nat) : MacroM (TSyntax `tactic) := do
    if i < xs.size then
      let xi := xs[i]!
      let yi := ys[i]!
      -- Recursively build the tactic for the inner levels
      let innerTactic ← go (i + 1)

      -- Use the standard `cases ... with` syntax, which correctly handles scoping.
      -- The `innerTactic` is now placed *inside* the `bitvec` branch's scope.
      `(tactic|
        cases $xi:ident with
        | bitvec $yi => $innerTactic:tactic
        | poison => simp [iN_unwrap_inst])
    else
      -- The base case when all variables have been processed.
      `(tactic| skip)

  go 0 -/

--syntax "poison_unroll" (ppSpace colGt ident)* " =>" (ppSpace colGt ident)* : tactic

elab "poison_unroll" xs:(ppSpace colGt ident)* " =>" as:(ppSpace colGt ident)* : tactic => do

  unless xs.size == as.size do
    throwError s!"poison_unroll: got {xs.size} variables but {as.size} names"

  (xs.zip as).forM $ fun (x, a) => do
    evalTactic (← `(tactic| by_cases ($x).poison))
    evalTactic (← `(tactic| . simp [iN_unwrap_inst, *]))
    evalTactic (← `(tactic| let $a := ($x).bitvec))

  evalTactic (← `(tactic| simp [iN_unwrap_inst, *]))


/- macro_rules
| `(tactic| poison_unroll $xs:ident* => $ys:ident*) => do
  unless xs.size == ys.size do
    Macro.throwError s!"poison_unroll: got {xs.size} variables but {ys.size} names"

  -- This recursive function now returns a `TSyntax `tactic`, which is the correct
  -- type for splicing into a tactic block.
  let rec go (i : Nat) : MacroM (TSyntax `tactic) := do
    if i < xs.size then
      let xi := xs[i]!
      let yi := ys[i]!
      -- Recursively build the tactic for the inner levels
      let innerTactic ← go (i + 1)

      -- Use the standard `cases ... with` syntax, which correctly handles scoping.
      -- The `innerTactic` is now placed *inside* the `bitvec` branch's scope.
      `(tactic|
        cases $xi:ident with
        | bitvec $yi => $innerTactic:tactic
        | poison => simp [iN_unwrap_inst])
    else
      -- The base case when all variables have been processed.
      `(tactic| skip)

  go 0 -/

/--
Clears obvious contradictory goals with hypotheses of the form
`poison = bitvec a` or `bitvec a = poison`.
-/
elab "clear_poison_eq" : tactic => do
  withMainContext do
    let mainGoal ← getMainGoal

    let ctx ← getLCtx
    ctx.forM $ fun (decl : Lean.LocalDecl) => do
      let declExpr := decl.toExpr
      let declType ← Lean.Meta.inferType declExpr
      let (fn, args) := declType.getAppFnArgs

      match fn, args with
      | `Eq, #[_, lhs, rhs] =>

        -- heq✝ : poison = bitvec a✝
        -- heq✝ : poison = bitvec b✝

        let isName (e : Expr) (n : Name) : Bool :=
          e.getAppFn.constName? == some n

        let isPoison (e : Expr) : Bool := isName e ``iN.poison
        let isBV (e : Expr) : Bool := isName e ``iN.bitvec

        if (isPoison lhs && isBV rhs) || (isPoison rhs && isBV lhs) then
          let fvarId := decl.fvarId
          -- clear obvious contradiction
          let newSubgoals ← mainGoal.cases fvarId
          replaceMainGoal (newSubgoals.map (·.mvarId)).toList
          return
      | _, _ => pure ()
