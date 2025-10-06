import Lean
import theorems.iN.iN_def
import theorems.iN.iN_rewrite

open Lean Elab Tactic Meta

/- set_option trace.Meta.opti true -/
initialize registerTraceClass `Meta.opti

structure OptResult where
  /-- The simplified version of `e` -/
  expr : Expr
  /-- A proof that `$e ~> $expr`, where the simplified expression is on the RHS.
  If `none`, the proof is assumed to be `Rewrite.refl`. -/
  proof? : Option Expr := none
deriving Inhabited

structure OptProcDecl where
  declName : Name
deriving Inhabited

abbrev OptProc := Expr → MetaM (Option OptResult)

abbrev OptProcList := Array (OptProcDecl × OptProc)

structure OptState where
  -- TODO memo
  -- lhs ~> rhs
  rewrites : Array Expr
  procs : OptProcList
deriving Inhabited

abbrev OptM := StateRefT OptState MetaM

structure OptProcDeclExtState where
  entries : PHashMap Name Unit := {}
deriving Inhabited

def OptProcDecl.lt (decl₁ decl₂ : OptProcDecl) : Bool :=
  Name.quickLt decl₁.declName decl₂.declName

initialize optProcDeclExt : PersistentEnvExtension OptProcDecl OptProcDecl OptProcDeclExtState ←
  registerPersistentEnvExtension {
    mkInitial       := return { entries := {} }
    addImportedFn   := fun _ => return { entries := {} }
    addEntryFn      := fun s d => { s with entries := s.entries.insert d.declName () }
    exportEntriesFn := fun s =>
      let result := s.entries.foldl (init := #[]) fun result declName key => result.push { declName }
      result.qsort OptProcDecl.lt
  }

def isOptProc (declName : Name) : CoreM Bool := do
  let env ← getEnv
  match env.getModuleIdxFor? declName with
    | some modIdx => do
      let some decl := (optProcDeclExt.getModuleEntries env modIdx).binSearch { declName } OptProcDecl.lt
        | pure false
      pure true
    | none        => pure ((optProcDeclExt.getState env).entries.find? declName).isSome

def registerOptProc (declName : Name) : CoreM Unit := do
  let env ← getEnv
  unless (env.getModuleIdxFor? declName).isNone do
    throwError "invalid optProc declaration '{declName}', function declaration is in an imported module"
  if (← isOptProc declName) then
    throwError "invalid optProc declaration '{declName}', it has already been declared"
  modifyEnv fun env => optProcDeclExt.modifyState env fun s => { s with entries := s.entries.insert declName () }

unsafe def getOptProcsImpl : CoreM OptProcList := do
  let ctx ← readThe Lean.ImportM.Context
  let mut procs : Array (OptProcDecl × OptProc) := #[]

  let env ← getEnv
  let t := optProcDeclExt.getState env
  for (declName, _) in t.entries do
    let optproc : OptProc ← match ctx.env.find? declName with
    | none      => throwError "unknown constant"
    | some info =>
      match info.type with
      | .const ``OptProc _ =>
        let .ok v := ctx.env.evalConst OptProc ctx.opts declName
          | throwError ("failed to evaluate optproc '" ++ toString declName ++ "'")

        pure v
      | _ => throwError "unexpected type at optproc"

    procs := procs.push ({ declName }, optproc)

  return procs

@[implemented_by getOptProcsImpl]
opaque getOptProcs : CoreM OptProcList

/- Proves `f poison = poison`. -/
def proveCongruence (motive : Expr) (n : Expr) : MetaM Expr := do
  let poison := mkApp (.const ``poison []) n
  let poison_app := mkApp motive poison
  let goalType ← mkEq poison_app poison

  let proofMVar ← mkFreshExprMVar goalType .synthetic `h_cong_proof

  let ctx ← Simp.mkContext
    (config := { beta := true })
    (simpTheorems := #[← getSimpTheorems, ← iNInst.getTheorems])
    (congrTheorems := (← getSimpCongrTheorems))
  let (result?, _) ← simpGoal proofMVar.mvarId! ctx

  if let some _ := result? then
    /- throwTactic `opt_rewrite x
      m!"unable to prove congruence goal `motive poison = poison` automatically with `simp [simp_iN]`" -/
    throwError "unable to prove congruence goal `motive poison = poison` automatically with `simp [simp_iN]`"

  instantiateMVars proofMVar
