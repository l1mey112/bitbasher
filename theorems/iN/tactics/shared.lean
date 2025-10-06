import Lean
import theorems.iN.iN_def
import theorems.iN.iN_rewrite

open Lean Elab Tactic Meta

/- set_option trace.Meta.opti true -/
initialize registerTraceClass `Meta.opti

structure OptProcDecl where
  declName : Name
  keys     : Array SimpTheoremKey
deriving Inhabited

structure OptProcDeclExtState where
  entries : PHashMap Name (Array SimpTheoremKey) := {}
deriving Inhabited

def OptProcDecl.lt (decl₁ decl₂ : OptProcDecl) : Bool :=
  Name.quickLt decl₁.declName decl₂.declName

initialize optProcDeclExt : PersistentEnvExtension OptProcDecl OptProcDecl OptProcDeclExtState ←
  registerPersistentEnvExtension {
    mkInitial       := return { entries := {} }
    addImportedFn   := fun _ => return { entries := {} }
    addEntryFn      := fun s d => { s with entries := s.entries.insert d.declName d.keys }
    exportEntriesFn := fun s =>
      let result := s.entries.foldl (init := #[]) fun result declName keys => result.push { declName, keys }
      result.qsort OptProcDecl.lt
  }

def getOptProcDeclKeys? (declName : Name) : CoreM (Option (Array SimpTheoremKey)) := do
  let env ← getEnv
  let keys? ← match env.getModuleIdxFor? declName with
    | some modIdx => do
      let some decl := (optProcDeclExt.getModuleEntries env modIdx).binSearch { declName, keys := #[] } OptProcDecl.lt
        | pure none
      pure (some decl.keys)
    | none        => pure ((optProcDeclExt.getState env).entries.find? declName)
  if let some keys := keys? then
    return some keys
  else
    return none

def isOptProc (declName : Name) : CoreM Bool :=
  return (← getOptProcDeclKeys? declName).isSome

def registerOptProc (declName : Name) (keys : Array SimpTheoremKey) : CoreM Unit := do
  let env ← getEnv
  unless (env.getModuleIdxFor? declName).isNone do
    throwError "invalid optProc declaration '{declName}', function declaration is in an imported module"
  if (← isOptProc declName) then
    throwError "invalid optProc declaration '{declName}', it has already been declared"
  modifyEnv fun env => optProcDeclExt.modifyState env fun s => { s with entries := s.entries.insert declName keys }

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
