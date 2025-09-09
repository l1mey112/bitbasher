import theorems.Core.Attrs.Attrs
import theorems.Core.Anything
import theorems.Core.iN
import theorems.Core.iN_lemmas

inductive Bits : Nat → Prop where
  | i1 : Bits 1
  | i8 : Bits 8
  | i16 : Bits 16
  | i32 : Bits 32
  | i64 : Bits 64
