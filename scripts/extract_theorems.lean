import Lean
import Lean.Util.SearchPath
import theorems.Core.Attrs.Attrs

open Lean Core Elab

def main (_args : List String) : IO UInt32 := do
  let modules := #[`theorems]
  initSearchPath (← findSysroot)

  let env ← importModules (modules.map ({module := ·})) {} (trustLevel := 1024) (loadExts := true)
  let ctx : Context := {fileName := "", fileMap := default}
  let state : State := {env}

  let entries ← Prod.fst <$> (Meta.MetaM.toIO · ctx state) do
    pure $ ruleEntries.getState (← getEnv)

  let stdout ← IO.getStdout

  /- This is a really simple thing that I don't know how to do in Lean.
    Why does `Array.mapIdxM` exist but not `Array.forIdxM` ?? -/

  let rec wr (idx : Nat) (h : idx ≤ entries.size) := do
    if hh : idx == entries.size then
      return
    else
      have el : idx < entries.size := by grind

      let entry := entries[idx]'el
      stdout.writeJson (toJson entry)

      if idx + 1 != entries.size then
        stdout.putStr ","

      wr (idx + 1) (by grind)

  stdout.putStr "["
  wr 0 (by grind)
  stdout.putStr "]"

  pure 0
