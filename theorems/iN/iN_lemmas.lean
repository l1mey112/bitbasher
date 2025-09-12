import theorems.iN.SimpSets
import theorems.iN.iN_def
import theorems.iN.iN_tactics
import theorems.iN.iN_rewrite
import theorems.Core.Attrs.Attrs

/-- The supported bit sizes. Proofs do not need to prove ∀n : Nat. -/
inductive Bits : Nat → Prop where
  | i1 : Bits 1
  | i8 : Bits 8
  | i16 : Bits 16
  | i32 : Bits 32
  | i64 : Bits 64
  | i128 : Bits 128

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

theorem BitVec.saddOverflow_chain_assoc_monotone {n} {hn : Bits n} (a b c : BitVec n)
    (h : a.msb = b.msb ∧ b.msb = c.msb)

    : (a.saddOverflow b || (a + b).saddOverflow c) =
      (b.saddOverflow c || a.saddOverflow (b + c)) := by

  cases hn
  case i1   => bv_check "../../lrat/BitVec.saddOverflow_assoc_monotone-45-15.lrat"
  case i8   => bv_check "../../lrat/BitVec.saddOverflow_assoc_monotone-46-15.lrat"
  case i16  => bv_check "../../lrat/BitVec.saddOverflow_assoc_monotone-47-15.lrat"
  case i32  => bv_check "../../lrat/BitVec.saddOverflow_assoc_monotone-48-15.lrat"
  case i64  => bv_check "../../lrat/BitVec.saddOverflow_assoc_monotone-49-15.lrat"
  case i128 => bv_check "../../lrat/BitVec.saddOverflow_assoc_monotone-50-15.lrat"

/- theorem test : ∃ (n : Nat) (a b c : BitVec n),
    ¬((a.saddOverflow b || (a + b).saddOverflow c) ==
      (b.saddOverflow c || a.saddOverflow (b + c))) := by

  exists 8, 127#8, 1#8, -1#8 -/

theorem BitVec.uaddOverflow_chain_assoc {n} {hn : Bits n} (a b c : BitVec n)
    : (a.uaddOverflow b || (a + b).uaddOverflow c) =
      (b.uaddOverflow c || a.uaddOverflow (b + c)) := by

  cases hn
  case i1   => bv_check "../../lrat/iN_lemmas.lean-BitVec.uaddOverflow_chain_assoc-57-15.lrat"
  case i8   => bv_check "../../lrat/iN_lemmas.lean-BitVec.uaddOverflow_chain_assoc-58-15.lrat"
  case i16  => bv_check "../../lrat/iN_lemmas.lean-BitVec.uaddOverflow_chain_assoc-59-15.lrat"
  case i32  => bv_check "../../lrat/iN_lemmas.lean-BitVec.uaddOverflow_chain_assoc-60-15.lrat"
  case i64  => bv_check "../../lrat/iN_lemmas.lean-BitVec.uaddOverflow_chain_assoc-61-15.lrat"
  case i128 => bv_check "../../lrat/iN_lemmas.lean-BitVec.uaddOverflow_chain_assoc-62-16.lrat"

namespace iN

@[simp, grind =]
theorem eq_bitvec_inj {n} {a b : BitVec n} :
    ((bitvec a : iN n) = (bitvec b : iN n)) ↔ a = b := by

  constructor
  · intro h
    injection h
  . intro h
    rw [h]

@[simp]
theorem poisonWrapper_poison_left {n} {k} {g : BitVec n → BitVec n → iN k} {b : iN n} :
  iN.poisonWrapper g poison b = poison := by simp [iN.poisonWrapper]

@[simp]
theorem poisonWrapper_poison_right {n} {k} {g : BitVec n → BitVec n → iN k} {a : iN n} :
  iN.poisonWrapper g a poison = poison := by cases a <;> rfl

@[simp]
theorem poisonWrapper_bitvec_left {n} {k} {g : BitVec n → BitVec n → iN k} {a : BitVec n} {b : iN n} :
  iN.poisonWrapper g (bitvec a) b = match b with
    | poison => poison
    | bitvec b' => g a b' := by cases b <;> rfl

@[simp]
theorem poisonWrapper_bitvec_right {n} {k} {g : BitVec n → BitVec n → iN k} {a : iN n} {b : BitVec n} :
  iN.poisonWrapper g a (bitvec b) = match a with
    | poison => poison
    | bitvec a' => g a' b := by cases a <;> rfl

@[simp]
theorem poisonWrapper_bitvec {n} {k} {g : BitVec n → BitVec n → iN k} {a b : BitVec n} :
  iN.poisonWrapper g (bitvec a) (bitvec b) = g a b := by cases a <;> rfl

/-- Simplifying lemma about poisonable equations of the form `(a ⋄₁ b) ⋄₂ c`. -/
@[simp]
theorem poisonPreconditions_match_wrapper_assoc_left {n}
    (isPoison₁ : BitVec n → BitVec n → Bool)
    (isPoison₂ : BitVec n → BitVec n → Bool)
    (a b c : BitVec n)
    (op₁ : BitVec n → BitVec n → BitVec n)
    (op₂ : BitVec n → BitVec n → BitVec n)
    : (match iN.poisonPreconditions isPoison₁ op₁ a b with
      | poison => poison
      | bitvec ab' => iN.poisonPreconditions isPoison₂ op₂ ab' c)

      = bif isPoison₁ a b || isPoison₂ (op₁ a b) c then
        poison
      else
        bitvec (op₂ (op₁ a b) c) := by

  unfold iN.poisonPreconditions
  cases isPoison₁ a b
  . simp
  . simp

/-- Simplifying lemma about poisonable equations of the form `a ⋄₁ (b ⋄₂ c)`. -/
@[simp]
theorem poisonPreconditions_match_wrapper_assoc_right {n}
    (isPoison₁ : BitVec n → BitVec n → Bool)
    (isPoison₂ : BitVec n → BitVec n → Bool)
    (a b c : BitVec n)
    (op₁ : BitVec n → BitVec n → BitVec n)
    (op₂ : BitVec n → BitVec n → BitVec n)
    : (match iN.poisonPreconditions isPoison₂ op₂ b c with
      | poison => poison
      | bitvec bc' => iN.poisonPreconditions isPoison₁ op₁ a bc')

      = bif isPoison₂ b c || isPoison₁ a (op₂ b c) then
        poison
      else
        bitvec (op₁ a (op₂ b c)) := by

  unfold iN.poisonPreconditions
  cases isPoison₂ b c
  . simp
  . simp

@[simp]
theorem bitvec_cond {n} (c : Bool) (t e : BitVec n) :
    cond c (bitvec t) (bitvec e) = bitvec (cond c t e) := by
  cases c <;> rfl

/-- Forces unfolds when about to be simplified -/
@[simp]
theorem poisonPreconditions_rewrite_unfold {n} (a b : BitVec n) (c : iN n)
    (isPoison : BitVec n → BitVec n → Bool) (op : BitVec n → BitVec n → BitVec n)
    : (iN.poisonPreconditions isPoison op a b ~> c) =
      ((if isPoison a b then poison else bitvec (op a b)) ~> c) := by

  unfold iN.poisonPreconditions
  rfl

/-- Forces unfolds when about to be simplified -/
@[simp]
theorem poisonPreconditions_rewrite_iff_unfold_left {n} (a b : BitVec n) (c : iN n)
    (isPoison : BitVec n → BitVec n → Bool) (op : BitVec n → BitVec n → BitVec n)
    : (iN.poisonPreconditions isPoison op a b <~> c) =
      ((if isPoison a b then poison else bitvec (op a b)) <~> c) := by

  unfold iN.poisonPreconditions
  rfl

/-- Forces unfolds when about to be simplified -/
@[simp]
theorem poisonPreconditions_rewrite_iff_unfold_right {n} (a b : BitVec n) (c : iN n)
    (isPoison : BitVec n → BitVec n → Bool) (op : BitVec n → BitVec n → BitVec n)
    : (c <~> iN.poisonPreconditions isPoison op a b) =
      (c <~> (if isPoison a b then poison else bitvec (op a b))) := by

  unfold iN.poisonPreconditions
  rfl

/- @[grind =]
theorem addNswBV_comm {n} {a b : BitVec n}
    : iN.addNswBV a b = iN.addNswBV b a := by

  simp only [iN_to_bitvec]
  rw [BitVec.saddOverflow_comm]
  split <;> try simp

  -- h✝ : ¬b.saddOverflow a = true
  -- ⊢ a + b = b + a
  grind

@[grind =]
theorem addNuwBV_comm {n} {a b : BitVec n}
    : iN.addNuwBV a b = iN.addNuwBV b a := by

  simp only [iN_to_bitvec]
  rw [BitVec.uaddOverflow_comm]
  split <;> try simp

  -- h✝ : ¬b.uaddOverflow a = true
  -- ⊢ a + b = b + a
  grind -/

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
