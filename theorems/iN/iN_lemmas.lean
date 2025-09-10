import theorems.iN.SimpSets
import theorems.iN.iN_def
import theorems.iN.iN_tactics
import theorems.iN.iN_rewrite
import theorems.Core.Attrs.Attrs

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

namespace iN

@[grind =]
theorem addNswBV_comm {n} {a b : BitVec n}
    : iN.addNswBV a b = iN.addNswBV b a := by

  simp [iN_to_bitvec]
  rw [BitVec.saddOverflow_comm]
  split <;> try simp

  -- h✝ : ¬b.saddOverflow a = true
  -- ⊢ a + b = b + a
  grind

@[grind =]
theorem addNuwBV_comm {n} {a b : BitVec n}
    : iN.addNuwBV a b = iN.addNuwBV b a := by

  simp [iN_to_bitvec]
  rw [BitVec.uaddOverflow_comm]
  split <;> try simp

  -- h✝ : ¬b.uaddOverflow a = true
  -- ⊢ a + b = b + a
  grind

end iN

/- @[grind =]
theorem saddOverflow_comm_tete {n} (a b : BitVec n)
    : a.saddOverflow b = true ↔ b.saddOverflow a = true := by

  unfold BitVec.saddOverflow at *
  grind -/

/- theorem saddOverflow_contra {n} (a b : BitVec n)
    :  -/

/- @[simp]
theorem iN_contra {n} {a : BitVec n}
    {h : (poison : iN n) = (bitvec a : iN n)} : False := by

  cases h -/

/- theorem test_without {n} (x : iN n) : iN.shlNsw x 0 = x := by
  simp [iN_unwrap_poison]
  cases x with
  | poison => rfl
  | bitvec a => simp [iN_to_bitvec]

/- theorem com {n} (x y : iN n)
    : x + y = y + x := by

  cases x with
  | poison => rfl

  simp [iN_to_bitvec]
 -/

/- @[simp]
theorem com {n} (x : iN n) (val : Nat)
  : ((no_index OfNat.ofNat val) : iN n) + x
    = x + ((no_index OfNat.ofNat val) : iN n) := by
  cases x with
  | poison => rfl
  | bitvec a =>
    simp [iN_to_bitvec]
    apply BitVec.add_comm -/


@[simp]
theorem com0 {n} (x : iN n) (val : Nat)
  : lit(val) + x = x + lit(val) := by
  cases x with
  | poison => rfl
  | bitvec a =>
    simp [iN_to_bitvec]
    apply BitVec.add_comm

-- @bitvec n 23#↑n : iN n

theorem test {n} (x : iN n) : x + x = x + 23 := by

  simp -/
