import Lean
import theorems.Core.Attrs.Rule

open Lean Parser Elab Meta

structure Opts where
  /-- Is a normalising rule. -/
  is_ideal : Bool
  /-- Match on constant arguments. Indices into `Rule.inputs`. -/
  const_inputs : Array Nat
deriving Lean.ToJson, Inhabited, Repr

def Opts.toString (opts : Opts) : String := Id.run do
  let mut s := ""

  if opts.is_ideal then
    s := s ++ "ideal"

  if h : opts.const_inputs.size > 0 then
    s := s ++ s!" const (%{opts.const_inputs[0]}"
      ++ opts.const_inputs[1:].foldl (s!"{·}, %{·}") ""
      ++ ")"

  return s

instance : ToString Opts where
  toString := Opts.toString

structure Entry where
  name : Name
  filename : String
  line : Option Nat
  opts : Opts
  rule : Rule
deriving Lean.ToJson

initialize rule_entries : SimplePersistentEnvExtension Entry (Array Entry) ←
  registerSimplePersistentEnvExtension {
    name := `rule_entries
    addImportedFn := Array.flatMap id
    addEntryFn    := Array.push
  }

syntax (name := rule)
  "rule"
  ("ideal"
    ("const" "(" withoutPosition(num+) ")")?
  )? : attr

def Array.hasDuplicates {α : Type} [Hashable α] [BEq α] (a : Array α) : Bool :=
  let rec go (i : Nat) (seen : Std.HashSet α) : Bool :=
    if h : i < a.size then
      let x := a[i]'h
      if seen.contains x then true else go (i+1) (seen.insert x)
    else
      false
  go 0 {}

def parseRuleAttr (stx : Syntax) (rule : Rule) : MetaM Opts := do
  match stx with
  | `(rule|rule) => return default
  | `(rule|rule ideal) => return { (default : Opts) with is_ideal := true }
  | `(rule|rule ideal const ($[$xs:num]*)) =>
    let nats := xs.map (·.getNat)

    if nats.hasDuplicates then
      throwError "Duplicate const reference"

    if nats.any (· >= rule.inputs.size) then
      throwError "Number out of range"

    return { (default : Opts) with
      is_ideal := true,
      const_inputs := nats,
    }
  | _ => throwErrorAt stx "Invalid syntax"

syntax (name := inst) "inst" str : attr

initialize valid_instructions_env : SimplePersistentEnvExtension (Name × String) (Std.HashMap Name String) ←
  let addEntryFn | m, (n3, n4) => m.insert n3 n4
  registerSimplePersistentEnvExtension {
    name := `valid_instructions
    addImportedFn := mkStateFromImportedEntries addEntryFn {}
    addEntryFn
  }

initialize instAttr : Unit ←
  registerBuiltinAttribute {
    name  := `inst
    descr := "tags theorems to be used as instructions"
    applicationTime := .afterCompilation
    add   := fun declName stx _attrKind => do
      let strstx := stx[1]!
      let some str := strstx.isStrLit? | throwErrorAt strstx "expected string literal"

      let info ← getConstInfo declName
      match info with
      | .defnInfo _ => pure ()
      | _ => throwErrorAt stx "@[inst] is only allowed on definitions"

      let s := valid_instructions_env.getState (← getEnv)
      if s.valuesArray.any (· == str) then
        throwErrorAt strstx "instruction with name {str} already defined"

      modifyEnv fun env =>
         valid_instructions_env.addEntry env (declName, str)
  }

initialize ruleAttr : Unit ←
  registerBuiltinAttribute {
    name  := `rule
    descr := "tags theorems to be used as equalities and rewrite rules if `ideal` is present"
    applicationTime := .afterCompilation
    add   := fun declName stx _attrKind => do
      let ctx ← read
      let filename := ctx.fileName
      let line := stx.getPos?.map λ pos => ctx.fileMap.toPosition pos |>.line

      discard <| MetaM.run do
        let axioms ← collectAxioms declName
        for a in axioms do
          if not (a ∈ [``propext, ``Classical.choice, ``Quot.sound, ``Lean.ofReduceBool]) then
            throwError s!"rule uses a prohibited axiom: {a}"

        let info ← getConstInfo declName
        let entry: Entry ← match info with
          | .thmInfo  (val : TheoremVal) =>
            let valid_instructions := valid_instructions_env.getState (← getEnv)
            let rule ← Rule.parseRule val.type valid_instructions
            let opts ← parseRuleAttr stx rule

            dbg_trace rule
            let ost := opts.toString
            if ost != "" then
              dbg_trace ost

            pure <| {
              name := val.name,
              filename := filename,
              line := line,
              opts := opts,
              rule := rule

              : Entry
            }
          | _ => throwError "@[rule] is only allowed on theorems"
  }
