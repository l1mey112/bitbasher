import Lean
import theorems.iN.iN_def

open Lean Elab Tactic Meta

-- https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Clearing.20obvious.20contradictions.20in.20cases.20of.20goals/near/538579820

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
