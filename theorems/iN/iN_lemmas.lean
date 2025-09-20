import theorems.iN.SimpSets
import theorems.iN.iN_def
import theorems.iN.iN_rewrite
import theorems.Core.Attrs.Attrs

/-- The supported bit sizes. Proofs do not need to prove ∀n : Nat. -/
inductive Bits : Nat → Prop where
  | i8 : Bits 8
  | i16 : Bits 16
  | i32 : Bits 32
  | i64 : Bits 64

/-- The supported bit sizes, with bool. Proofs do not need to prove ∀n : Nat. -/
inductive BitsBool : Nat → Prop where
  | i1 : BitsBool 1
  | i8 : BitsBool 8
  | i16 : BitsBool 16
  | i32 : BitsBool 32
  | i64 : BitsBool 64

@[grind =]
theorem BitVec.saddOverflow_comm {n} (a b : BitVec n)
    : a.saddOverflow b = b.saddOverflow a := by

  intros
  unfold BitVec.saddOverflow
  grind

@[grind =]
theorem BitVec.uaddOverflow_comm {n} (a b : BitVec n)
    : a.uaddOverflow b = b.uaddOverflow a := by

  intros
  unfold BitVec.uaddOverflow
  grind

theorem BitVec.saddOverflow_chain_assoc_monotone {n} {hn : BitsBool n} (a b c : BitVec n)
    (h : a.msb = b.msb ∧ b.msb = c.msb)

    : (a.saddOverflow b || (a + b).saddOverflow c) =
      (b.saddOverflow c || a.saddOverflow (b + c)) := by

  cases hn
  case i1   => bv_check "../../lrat/BitVec.saddOverflow_assoc_monotone-45-15.lrat"
  case i8   => bv_check "../../lrat/BitVec.saddOverflow_assoc_monotone-46-15.lrat"
  case i16  => bv_check "../../lrat/BitVec.saddOverflow_assoc_monotone-47-15.lrat"
  case i32  => bv_check "../../lrat/BitVec.saddOverflow_assoc_monotone-48-15.lrat"
  case i64  => bv_check "../../lrat/BitVec.saddOverflow_assoc_monotone-49-15.lrat"
  --case i128 => bv_check "../../lrat/BitVec.saddOverflow_assoc_monotone-50-15.lrat"

/- theorem test : ∃ (n : Nat) (a b c : BitVec n),
    ¬((a.saddOverflow b || (a + b).saddOverflow c) ==
      (b.saddOverflow c || a.saddOverflow (b + c))) := by

  exists 8, 127#8, 1#8, -1#8 -/

theorem BitVec.uaddOverflow_chain_assoc {n} {hn : BitsBool n} (a b c : BitVec n)
    : (a.uaddOverflow b || (a + b).uaddOverflow c) =
      (b.uaddOverflow c || a.uaddOverflow (b + c)) := by

  cases hn
  case i1   => bv_check "../../lrat/iN_lemmas.lean-BitVec.uaddOverflow_chain_assoc-57-15.lrat"
  case i8   => bv_check "../../lrat/iN_lemmas.lean-BitVec.uaddOverflow_chain_assoc-58-15.lrat"
  case i16  => bv_check "../../lrat/iN_lemmas.lean-BitVec.uaddOverflow_chain_assoc-59-15.lrat"
  case i32  => bv_check "../../lrat/iN_lemmas.lean-BitVec.uaddOverflow_chain_assoc-60-15.lrat"
  case i64  => bv_check "../../lrat/iN_lemmas.lean-BitVec.uaddOverflow_chain_assoc-61-15.lrat"
  --case i128 => bv_check "../../lrat/iN_lemmas.lean-BitVec.uaddOverflow_chain_assoc-62-16.lrat"

/- theorem BitVec.saddOverflow_chain_assoc_monotone {n} {hn : Bits n} (a b c : BitVec n)
    (h : a.msb = b.msb ∧ b.msb = c.msb)

    : (a.saddOverflow b || (a + b).saddOverflow c) =
      (b.saddOverflow c || a.saddOverflow (b + c)) := by
 -/

@[simp]
theorem sadd_overflow_assoc_of_nonneg (a b c : BitVec 32) :
  a.slt 0#32 = false → b.slt 0#32 = false → c.slt 0#32 = false →
  ((a.saddOverflow b || (a + b).saddOverflow c) ↔ (b.saddOverflow c || a.saddOverflow (b + c))) := by

  bv_decide

@[simp]
theorem sadd_overflow_assoc_of_neg (x y z : BitVec 32) :
  x.slt 0#32 = true → y.slt 0#32 = true → z.slt 0#32 = true →
  ((x.saddOverflow y || (x + y).saddOverflow z) ↔ (y.saddOverflow z || x.saddOverflow (y + z))) := by

  bv_decide
