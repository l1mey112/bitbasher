import Lean

open Lean Meta

-- note to self, do not name this `iN_to_bitvec` as in simp invocations it the wrong identifier

initialize iNToBitVecExt : SimpExtension ←
  registerSimpAttr `iN_to_bitvec
    "simp lemmas converting `iN` goals to `BitVec` goals"

initialize iNUnwrapPoison : SimpExtension ←
  registerSimpAttr `iN_unwrap_poison
    "simp lemmas unwrapping initial poison matches in `iN` goals"
