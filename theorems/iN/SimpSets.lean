import Lean

open Lean Meta

/- initialize iNInst : SimpExtension ←
  registerSimpAttr `iN_unwrap_inst
    "simp lemmas unwrapping instructions" -/

initialize iNInst : SimpExtension ←
  registerSimpAttr `simp_iN
    "simp lemmas unwrapping instructions"
