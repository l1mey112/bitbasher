import Lean
import theorems.iN.iN_def
import theorems.iN.iN_rewrite
import theorems.iN.tactics.shared

open Lean Elab Tactic Meta Command

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
