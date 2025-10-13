import Lean
import theorems.iN.iN_def
import theorems.iN.iN_rewrite

open Lean Elab Tactic Meta Command

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
  qualifiedName : String
deriving Inhabited

abbrev OptProc := Expr → MetaM (Option OptResult)

abbrev OptProcList := Array (OptProcDecl × OptProc)

structure OptDecl where
  declName : Name
  qualifiedName : String
  line : Option Nat
  isIdeal : Bool
deriving Inhabited, Repr

instance : BEq OptDecl where
  beq := (·.declName == ·.declName)

abbrev OptTheorems := DiscrTree OptDecl

structure OptConfig where
  prove_rewrites : Bool := true
  procs : OptProcList
  theorems : OptTheorems
deriving Inhabited

structure OptState where
  -- TODO memo
  -- lhs ~> rhs
  rewrites : Array Expr
  memo : Std.HashMap Expr (Option OptResult)
deriving Inhabited

abbrev OptM := ReaderT OptConfig $ StateRefT OptState MetaM

structure OptProcDeclExtState where
  entries : PHashMap Name OptProcDecl := {}
deriving Inhabited

structure OptDeclExtState where
  entries : PHashMap Name OptDecl := {}
deriving Inhabited

def OptProcDecl.lt (decl₁ decl₂ : OptProcDecl) : Bool :=
  Name.quickLt decl₁.declName decl₂.declName

def OptDecl.lt (decl₁ decl₂ : OptDecl) : Bool :=
  Name.quickLt decl₁.declName decl₂.declName

def mkQualifiedNameStr (name module : Name) := module.toString ++ "." ++ name.getString!

initialize optProcDeclExt : PersistentEnvExtension OptProcDecl OptProcDecl OptProcDeclExtState ←
  registerPersistentEnvExtension {
    mkInitial       := return { entries := {} }
    addImportedFn   := fun _ => return { entries := {} }
    addEntryFn      := fun s d => { s with entries := s.entries.insert d.declName d }
    exportEntriesFn := fun s =>
      let result := s.entries.foldl (init := #[]) fun result declName key => result.push key
      result.qsort OptProcDecl.lt
  }

def isOptProc (declName : Name) : CoreM Bool := do
  let env ← getEnv
  match env.getModuleIdxFor? declName with
    | some modIdx => do
      let some decl := (optProcDeclExt.getModuleEntries env modIdx).binSearch { declName, qualifiedName := "" : OptProcDecl } OptProcDecl.lt
        | pure false
      pure true
    | none        => pure ((optProcDeclExt.getState env).entries.find? declName).isSome

def registerOptProc (declName : Name) : CoreM Unit := do
  let env ← getEnv
  let module ← getMainModule
  let qualifiedName := mkQualifiedNameStr declName module

  unless (env.getModuleIdxFor? declName).isNone do
    throwError "invalid optProc declaration '{declName}', function declaration is in an imported module"
  if (← isOptProc declName) then
    throwError "invalid optProc declaration '{declName}', it has already been declared"
  modifyEnv fun env => optProcDeclExt.modifyState env fun s => { s with entries := s.entries.insert declName { declName, qualifiedName } }

unsafe def getOptProcsImpl : CoreM OptProcList := do
  let ctx ← readThe Lean.ImportM.Context
  let mut procs : Array (OptProcDecl × OptProc) := #[]

  let env ← getEnv
  let t := optProcDeclExt.getState env
  for (declName, decl) in t.entries do
    let optproc : OptProc ← match ctx.env.find? declName with
    | none      => throwError "unknown constant"
    | some info =>
      match info.type with
      | .const ``OptProc _ =>
        let .ok v := ctx.env.evalConst OptProc ctx.opts declName
          | throwError ("failed to evaluate optproc '" ++ toString declName ++ "'")

        pure v
      | _ => throwError "unexpected type at optproc"

    procs := procs.push (decl, optproc)

  return procs

@[implemented_by getOptProcsImpl]
opaque getOptProcs : CoreM OptProcList

initialize optDeclExt : PersistentEnvExtension OptDecl OptDecl OptDeclExtState ←
  registerPersistentEnvExtension {
    mkInitial       := return { entries := {} }
    addImportedFn   := fun _ => return { entries := {} }
    addEntryFn      := fun s d => { s with entries := s.entries.insert d.declName d }
    exportEntriesFn := fun s =>
      let result := s.entries.foldl (init := #[]) fun result declName key => result.push key
      result.qsort OptDecl.lt
  }

def getOptDecls : CoreM $ Array OptDecl := do
  let mut procs : Array OptDecl := #[]

  let env ← getEnv
  let t := optDeclExt.getState env
  for (_, d) in t.entries do
    procs := procs.push d

  return procs

syntax (name := optProcPattern) "optproc% " " => " ident : command
/--
A user-defined optimisation procedure used by the `opt` tactic, and its variants.
-/
syntax (docComment)? attrKind "optproc " ident " := " term : command
/--
A user-defined optimisation procedure declaration. To activate this procedure in `opt` tactic,
we must provide it as an argument, or use the command `attribute` to set its `[opt]` attribute.
-/
syntax (docComment)? "optproc_decl " ident " := " term : command

macro_rules
  | `($[$doc?:docComment]? optproc_decl $n:ident := $body) => do
    let simprocType := `OptProc
    `($[$doc?:docComment]? def $n:ident : $(mkIdent simprocType) := $body
      optproc% => $n)

macro_rules
  | `($[$doc?:docComment]? $_:attrKind optproc $n:ident := $body) => do
     return mkNullNode <|
       #[(← `($[$doc?:docComment]? optproc_decl $n := $body))]

def checkOptprocType (declName : Name) : CoreM Bool := do
  let decl ← getConstInfo declName
  match decl.type with
  | .const ``OptProc _ => pure false
  | _ => throwError "unexpected type at '{declName}', 'Optproc' expected"

@[command_elab optProcPattern]
def elabOptprocPattern : CommandElab := fun stx => do
  let `(optproc% => $declName) := stx | throwUnsupportedSyntax
  liftTermElabM do
    let declName ← realizeGlobalConstNoOverload declName
    discard <| checkOptprocType declName
    registerOptProc declName

syntax (name := opt) "opt" ("ideal")? : attr

def validateOptTheorem (type : Expr) : MetaM Unit := do
  /- lhs ~> rhs, lhs <~> rhs -/

  /- ∀ (x : iN n) ..., lhs ~> rhs -/

  forallTelescope type fun _fvars body => do

    /- fvars.forM fun fvar => do
      let fvar_type ← inferType fvar
      let fvar_uni ← inferType fvar_type

      /- fvar_type = iN n, fvar_uni = Type
        fvar_type = (x > 2), fvar_uni = Prop -/

      sorry -/

    match_expr (← whnf body) with
    | Rewrite _ _ _ => pure ()
    | RewriteIff _ _ _ => pure ()
    | _ =>
      throwError "expected `~>` or `<~>` expression"

initialize optAttr : Unit ←
  registerBuiltinAttribute {
    name  := `opt
    descr := "tags theorems to be used as facts, and rewrite rules only if `ideal` is present"
    applicationTime := .afterCompilation
    add   := fun declName stx _attrKind => do
      let ctx ← read
      let filename := ctx.fileName

      let line := stx.getPos?.map λ pos => ctx.fileMap.toPosition pos |>.line
      let module ← getMainModule

      discard <| MetaM.run do
        let axioms ← collectAxioms declName
        for a in axioms do
          if not (a ∈ [``propext, ``Classical.choice, ``Quot.sound, ``Lean.ofReduceBool]) then
            throwError s!"opt uses a prohibited axiom: {a}"

        let info ← getConstInfo declName
        let entry: OptDecl ← match info with
          | .thmInfo  (val : TheoremVal) =>
            let isIdeal := match stx with
            | `(opt|opt) => false
            | `(opt|opt ideal) => true
            | _ => unreachable!

            let name := val.name
            let qualifiedName := mkQualifiedNameStr name module

            validateOptTheorem val.type

            pure <| {
              declName,
              qualifiedName,
              line,
              isIdeal,

              : OptDecl
            }
          | _ => throwError "@[opt] is only allowed on theorems"

        modifyEnv fun env =>
          optDeclExt.addEntry env entry
  }

def getOptTheorems : MetaM OptTheorems := do
  let optDecls ← getOptDecls

  let mut optTheorems := default

  for t in optDecls do
    if !t.isIdeal then
      continue

    let val := mkConst t.declName []
    let type ← inferType val
    let (_, _, type) ← forallMetaTelescopeReducing type
    let type ← whnfR type

    let keys ← match_expr type with
    | Rewrite _ lhs _ => DiscrTree.mkPath lhs false
    | RewriteIff _ lhs _ => DiscrTree.mkPath lhs false
    | _ => unreachable!

    optTheorems := optTheorems.insertCore keys t

  return optTheorems

/-- Proves `f poison = poison`. -/
def proveCongruence (motive : Expr) (n : Expr) : MetaM Expr := do
  /- TODO make this function prove things nicely instead of unwrapping
    things down to the bone with simp which is slow and creates bloated
    proof terms -/

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
