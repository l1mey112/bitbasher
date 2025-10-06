import Lean
import theorems.iN.iN_def
import theorems.iN.iN_llvm
import theorems.iN.iN_lemmas
import theorems.iN.iN_rewrite

import theorems.iN.tactics.shared
import theorems.iN.tactics.iN_opt

open Lean Elab Tactic Meta

def isiNType (e : Expr) : MetaM Bool := do
  let eType ← inferType e
  let eType ← whnf eType
  if let .const name _ := eType.getAppFn then
    return name == ``iN
  return false

def getiNBitWidth (e : Expr) : MetaM Expr := do
  let eType ← inferType e
  let eType ← whnf eType
  match_expr eType with
  | iN w => return w
  | _ => throwError "expected iN type, got {eType}"

def getiNBitWidthFromType (ty : Expr) : MetaM Expr := do
  let ty ← whnf ty
  match_expr ty with
  | iN w => return w
  | _ => throwError "expected iN type, got {ty}"

namespace OptM

def runOptM (procs : OptProcList) (x : OptM α) : MetaM α :=
  x.run' { procs := procs, rewrites := #[] }

def handleOpt (expr : Expr) : OptM $ Option OptResult := do
  let procs := (← get).procs

  for (_, proc) in procs do
    match ← proc expr with
    | some { expr := expr', proof? } =>
      return some { expr := expr', proof? }
    | none => continue

  return none

def handleSingleRewrite (motive motive_wf : Expr) (hole : Expr) : OptM Expr := do
  /- try optimising, or do nothing -/
  let some optResult ← handleOpt hole
    | return hole

  let bw ← getiNBitWidth hole

  let proof ←
    match optResult.proof? with
    | some p => pure p
    | none   => pure (mkAppN (mkConst ``Rewrite.refl) #[bw, hole])

  -- optResult.proof : hole ~> optResult.expr
  -- ⊢ abstract hole ~> abstract optResult.expr
  let congrProof ← mkAppM ``Rewrite.congrApp #[motive, motive_wf, proof]
  trace[Meta.opti] m!"rewrite {hole} ~> {optResult.expr} by {proof}"

  -- append proof to state
  modify fun s => { s with rewrites := s.rewrites.push congrProof }
  return optResult.expr

def handleRewrites (abstract : Expr) (hole : Expr) : OptM Expr := do
  let bw ← getiNBitWidth hole
  let α := (Expr.app (.const `iN []) bw)

  -- optResult.proof : hole ~> optResult.expr
  -- ⊢ abstract hole ~> abstract optResult.expr
  let motive := Lean.mkLambda `_a BinderInfo.default α abstract
  let motive_wf ← proveCongruence motive bw

  let mut expr := hole

  repeat
    let newExpr ← handleSingleRewrite motive motive_wf expr
    if expr != newExpr then
      expr := newExpr
    else
      break

  return expr

def proveRewrites : OptM $ Option Expr := do
  let st ← get
  if st.rewrites.isEmpty then
    return none

  let mut finalProof := st.rewrites[0]!
  for proof in st.rewrites[1:] do
    finalProof ← mkAppM ``Rewrite.trans #[finalProof, proof]

  return some finalProof

end OptM


structure RewriteSite where
  /-- The expression with a subterm replaced by a bound variable `#0`.
      In this single-pass model, this is the *local* abstract, not the global one. -/
  abstract : Expr
  /-- The subterm that was replaced by the hole (`#0`). -/
  filler   : Expr
  deriving Inhabited

partial def walkAndTransform (e : Expr) : OptM Expr := do
  /- let cache ← IO.mkRef (α := Std.HashMap Expr Expr) {} -/

  let rec traverse (subExpr : Expr) (context : Expr → MetaM Expr) : OptM Expr := do
    /- if let some cachedResult := (← cache.get).get? subExpr then
      return (← context (← instantiateMVars cachedResult)) -/

    let rebuiltExpr ← match subExpr with
    | .app .. => do
      /- handle full applications as a single unit -/
      let fn := subExpr.getAppFn
      let args := subExpr.getAppArgs

      let mut args' := #[]
      for i in [:args.size] do
        let mut arg := args[i]!

        /- only process an argument if it is of type iN -/
        if !(arg.isLit || arg.isConst) && (← isiNType arg) then
          arg ← traverse arg (fun hole => context (mkAppN fn (args'.push hole ++ args.extract (i+1) args.size)))

        args' := args'.push arg

      pure $ mkAppN fn args'
    | .mdata _ i => traverse i context
    | _ => pure subExpr

    /- TODO we don't expect let binds or (definitely) lambdas in here -/
    let abstract ← context (mkBVar 0)
    let finalExpr ← OptM.handleRewrites abstract rebuiltExpr

    /- cache.modify (·.insert subExpr finalExpr) -/
    return finalExpr

  traverse e (fun hole => pure hole)

elab "⟨⟨" func:term "⟩⟩" : term => do
  let func ← Term.elabTerm func none
  let func ← unfoldDefinition func

  let optprocs ← getOptProcs

  let expr ← lambdaTelescope func fun xs A => OptM.runOptM optprocs do
    let B ← walkAndTransform A
    mkLambdaFVars xs B

  return expr

/-- On a goal of `lhs ~> rhs`, repeatedly apply rewrites to transform the goal into `lhs' ~> rhs`.  -/
elab "opti" : tactic => withMainContext do
  let mvarId ← getMainGoal
  mvarId.checkNotAssigned `opt

  let e ← getMainTarget
  let e ← instantiateMVars e

  let optprocs ← getOptProcs

  -- lhs ~> rhs
  let (_, lhs, rhs) ← match_expr e with
  | Rewrite n lhs rhs => pure (n, lhs, rhs)
  | _ => throwTacticEx `opt_rewrite mvarId m!"not a rewrite{indentExpr e}"

  let newGoal ← OptM.runOptM optprocs do
    let lhs' ← walkAndTransform lhs
    let some proof ← OptM.proveRewrites
      | throwTacticEx `opt mvarId "no rewrites were performed"

    -- Rewrite.trans (lhs ~> lhs') (lhs' ~> rhs) (lhs ~> rhs)
    --                             ^^^^^^^^^^^^^ create a new metavariable/goal

    trace[Meta.opti] m!"final proof term {proof}"

    let newGoalType ← mkAppM ``Rewrite #[lhs', rhs]
    let newGoalMVar ← mkFreshExprMVar (some newGoalType)
    let fullProof ← mkAppM ``Rewrite.trans #[proof, newGoalMVar]
    mvarId.assign fullProof

    pure newGoalMVar.mvarId!

  replaceMainGoal [newGoal]

macro "opt " : tactic =>
  `(tactic| (opti; try (with_reducible rfl)))

macro "opt_showcorrect " lhs:ident rhs:ident : tactic =>
  `(tactic| (unfold $lhs $rhs; solve
    | try (with_reducible rfl)
    | opti; try (with_reducible rfl)
  ))
