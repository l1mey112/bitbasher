import Lean
import theorems.Core.Attrs.Match

open Lean Parser Elab

inductive EntryVariant where
  | rewrite : Match → EntryVariant
deriving Lean.ToJson, Lean.FromJson, Inhabited

structure Entry where
  name : Name
  filename : String
  line : Option Nat
  variant : EntryVariant
deriving Lean.ToJson, Lean.FromJson, Inhabited

initialize entries : SimplePersistentEnvExtension Entry (Array Entry) ←
  registerSimplePersistentEnvExtension {
    name := `entries
    addImportedFn := Array.flatMap id
    addEntryFn    := Array.push
  }

def parseMatch (type : Expr) : MetaM (Option Match) := do
  /- forall {u : Nat} (a : BitVec u) (b : BitVec u) (con1 : BitVec u) (con2 : BitVec u), Eq.{1} (BitVec u) (...) (...) -/

  logInfo s!"{type}"

  Meta.forallTelescope type fun fvars rhs => do
    logInfo s!"fvars: {fvars}"
    logInfo s!"rhs: {rhs}"

    --logInfo s!"t: {fvars[0]!} {fvars[0]!.fvarId!.name}"

    let fvar_types ← fvars.mapM Meta.inferType
    logInfo s!"types are {fvar_types}"

    -- types are #[Nat, BitVec _uniq.199, BitVec _uniq.199, BitVec _uniq.199, BitVec _uniq.199]



    /- match fvars with
    | #[g, magma, lhsv] => parse rhs g magma lhsv false
    | #[g, magma, finite, lhsv] =>
      let (.app (.const `Finite _) _) := ← Meta.inferType finite | return none
      parse rhs g magma lhsv true
    | _ => return none -/

  return Match.mk

initialize rewriteAttr : Unit ←
  registerBuiltinAttribute {
    name  := `rewrite
    descr := "tags theorems to be used as rewrite rules"
    applicationTime := .afterCompilation
    add   := fun declName stx _attrKind => do
      let ctx ← read
      let filename := ctx.fileName
      let line := stx.getPos?.map λ pos => ctx.fileMap.toPosition pos |>.line

      logInfo s!"File: {filename}, Line: {line}"

      discard <| Lean.Meta.MetaM.run do
        let info ← getConstInfo declName
        let entry: Entry ← match info with
            | .thmInfo  (val : TheoremVal) =>
              if let some thing ← parseMatch val.type then
                pure <| ⟨val.name, filename, line, .rewrite thing⟩
              else
                throwError "failed to match type of @[rewrite] theorem"
            | _ => throwError "@[rewrite] is only allowed on theorems"

        let axioms ← Lean.collectAxioms declName
        for a in axioms do
          if not (a ∈ [``propext, ``Classical.choice, ``Quot.sound]) then
            throwError s!"declaration uses a prohibited axiom: {a}"

        logInfo s!"Entry: {entry.name}"

        modifyEnv fun env =>
         entries.addEntry env entry
  }

def extractRewrites {m : Type → Type} [Monad m] [MonadEnv m] [MonadError m] :
    m (Array Entry) := do
  return entries.getState (← getEnv)
