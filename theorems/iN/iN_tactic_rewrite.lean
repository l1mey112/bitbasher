import Lean
import theorems.iN.iN_def
import theorems.iN.iN_rewrite

open Lean Elab Tactic Meta

/-- On a goal of `lhs ~> rhs`, apply a rewrite of the form `x ~> y`.  -/
elab "apply_rewrite" t:term : tactic => withMainContext do
  let mvarId ← getMainGoal

  let matchRewrite (e : Expr) : MetaM (Expr × Expr × Expr) := do
    match_expr e with
    | Rewrite n lhs rhs => return (n, lhs, rhs)
    | _ => throwTacticEx `apply_rewrite mvarId m!"not a rewrite{indentExpr e}"

  let heq ← elabTerm t none true

  --let heqIn := heq
  let heqType ← instantiateMVars (← inferType heq)
  let (newMVars, _, heqType) ← forallMetaTelescopeReducing heqType
  /- `∀ (x y : iN 32), expr` into `expr`. -/
  let heq := mkAppN heq newMVars

  let occs : Occurrences := .all
  let e ← getMainTarget
  let e ← instantiateMVars e

  let (n, lhs, rhs) ← matchRewrite e
  let (_, x, y) ← matchRewrite heqType

  -- h: x ~> y
  -- ⊢ lhs ~> rhs
  let lhsAbst ← kabstract lhs x occs
  unless lhsAbst.hasLooseBVars do
    throwTacticEx `apply_rewrite mvarId m!"did not find instance of the pattern in the target expression{indentExpr lhs}"

  let α := (Expr.app (.const `iN []) n)
  let motive := Lean.mkLambda `_a BinderInfo.default α lhsAbst

  try
    check motive
  catch ex =>
    throwTacticEx `apply_rewrite mvarId m!"motive is not type correct:{indentD motive}\nError: {ex.toMessageData}"

  /- Proves `f poison = poison`. -/
  let proveCongruence (motive : Expr) : MetaM Expr := do
    let poison := mkApp (.const ``poison []) n
    let poison_app := mkApp motive poison
    let goalType ← mkEq poison_app poison

    let proofMVar ← mkFreshExprMVar goalType .synthetic `h_cong_proof

    let ctx ← Simp.mkContext
      (config := { beta := true })
      (simpTheorems := #[← getSimpTheorems, ← iNInst.getTheorems])
      (congrTheorems := (← getSimpCongrTheorems))
    let (result?, _) ← simpGoal proofMVar.mvarId! ctx

    if let some (_, x) := result? then
      throwTacticEx `apply_rewrite x
        m!"unable to prove congruence goal `motive poison = poison` automatically with `simp [simp_iN]`"

    instantiateMVars proofMVar

  let motiveProof ← proveCongruence motive
  let congrProof ← mkAppM ``Rewrite.congrApp #[motive, motiveProof, heq]

  /- Construct final proof term with `Rewrite.trans` and a new goal. -/
  let unreducedLhsNew := mkApp motive y
  let newGoalType := mkAppN (.const ``Rewrite []) #[n, unreducedLhsNew, rhs]
  let newGoalMVar ← mkFreshExprMVar (some newGoalType)
  let fullProof ← mkAppM ``Rewrite.trans #[congrProof, newGoalMVar]
  mvarId.assign fullProof

  let newGoalId := newGoalMVar.mvarId!
  let (n_new, unreducedLhs, rhs_new) ← matchRewrite (← newGoalId.getType)

  /- Beta reduce the annoying motive. -/
  let reducedLhs ← Core.betaReduce unreducedLhs
  let finalGoalType := mkAppN (.const ``Rewrite []) #[n_new, reducedLhs, rhs_new]
  let finalGoalId ← newGoalId.change finalGoalType

  replaceMainGoal [finalGoalId]

macro "apply_rw " t:term : tactic =>
  `(tactic| (apply_rewrite $t; try (with_reducible rfl)))
