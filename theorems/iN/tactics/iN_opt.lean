import Lean
import theorems.iN.iN_def
import theorems.iN.iN_rewrite
import theorems.iN.tactics.shared

open Lean Elab Tactic Meta Command

structure OptState where
  -- TODO memo
  -- lhs ~> rhs
  rewrites : Array Expr
deriving Inhabited

abbrev OptM := StateRefT OptState MetaM

structure OptResult where
  /-- The simplified version of `e` -/
  expr : Expr
  /-- A proof that `$e ~> $expr`, where the simplified expression is on the RHS.
  If `none`, the proof is assumed to be `Rewrite.refl`. -/
  proof? : Option Expr := none
deriving Inhabited

abbrev OptProc := Expr → OptM (Option OptResult)

syntax (name := optProcPattern) "optproc% " term " => " ident : command
/--
A user-defined optimisation procedure used by the `opt` tactic, and its variants.
-/
syntax (docComment)? attrKind "optproc " ident " (" term ")" " := " term : command
/--
A user-defined optimisation procedure declaration. To activate this procedure in `opt` tactic,
we must provide it as an argument, or use the command `attribute` to set its `[opt]` attribute.
-/
syntax (docComment)? "optproc_decl " ident " (" term ")" " := " term : command

macro_rules
  | `($[$doc?:docComment]? optproc_decl $n:ident ($pattern:term) := $body) => do
    let simprocType := `OptProc
    `($[$doc?:docComment]? def $n:ident : $(mkIdent simprocType) := $body
      optproc% $pattern => $n)

macro_rules
  | `($[$doc?:docComment]? $_:attrKind optproc $n:ident ($pattern:term) := $body) => do
     return mkNullNode <|
       #[(← `($[$doc?:docComment]? optproc_decl $n ($pattern) := $body))]

def checkOptprocType (declName : Name) : CoreM Bool := do
  let decl ← getConstInfo declName
  match decl.type with
  | .const ``OptProc _ => pure false
  | _ => throwError "unexpected type at '{declName}', 'Optproc' expected"

@[command_elab optProcPattern]
def elabOptprocPattern : CommandElab := fun stx => do
  let `(optproc% $pattern => $declName) := stx | throwUnsupportedSyntax
  liftTermElabM do
    let declName ← realizeGlobalConstNoOverload declName
    discard <| checkOptprocType declName
    let keys ← elabSimprocKeys pattern
    registerOptProc declName keys
