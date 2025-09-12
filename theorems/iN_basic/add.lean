import theorems.iN.iN

namespace iN

-- TODO mark not `@[rewrite]` but something for directional equality

@[grind]
theorem add_comm {n} (x y : iN n)
    : x + y = y + x := by

  poison_unroll x y => a b
  simp [iN_unwrap_inst]
  rw [BitVec.add_comm a b]

@[grind]
theorem addNsw_comm {n} (x y : iN n)
    : x +nsw y <~> y +nsw x := by

  poison_unroll x y => a b
  simp [iN_unwrap_inst]
  rw [BitVec.saddOverflow_comm a b]
  rw [BitVec.add_comm a b]

@[grind]
theorem addNuw_comm {n} (x y : iN n)
    : x +nuw y <~> y +nuw x := by

  poison_unroll x y => a b
  simp [iN_unwrap_inst]
  rw [BitVec.uaddOverflow_comm a b]
  rw [BitVec.add_comm a b]

@[grind]
theorem addNw_comm {n} (x y : iN n)
    : x +nw y <~> y +nw x := by

  poison_unroll x y => a b
  simp [iN_unwrap_inst]
  rw [BitVec.add_comm a b]
  rw [BitVec.saddOverflow_comm a b]
  rw [BitVec.uaddOverflow_comm a b]

@[grind]
theorem addNsw_refine {n} (x y : iN n)
  : x +nsw y ~> x + y := by

  poison_unroll x y => a b

  simp [iN_unwrap_inst]
  if h : a.saddOverflow b then
    simp [h]
  else
    simp [h]

@[grind]
theorem addNuw_refine {n} (x y : iN n)
  : x +nuw y ~> x + y := by

  poison_unroll x y => a b

  simp [iN_unwrap_inst]
  if h : a.uaddOverflow b then
    simp [h]
  else
    simp [h]

@[grind]
theorem addNw_refine {n} (x y : iN n)
  : x +nw y ~> x + y := by

  poison_unroll x y => a b

  simp [iN_unwrap_inst]
  if h1 : (a.saddOverflow b ∨ a.uaddOverflow b) then
    simp [h1]
  else
    simp [h1]

@[grind]
theorem add_assoc {n} (x y z : iN n)
    : (x + y) + z = x + (y + z) := by

  poison_unroll x y z => a b c
  simp [iN_unwrap_inst]
  rw [BitVec.add_assoc a b c]

@[grind]
theorem addNsw_not_assoc : ∃ (n : Nat) (x y z : iN n),
    ¬(x +nsw y) +nsw z <~> x +nsw (y +nsw z) := by

  exists 4
  exists 6, 5, bitvec (BitVec.neg 7)

  simp [iN_unwrap_inst, BitVec.saddOverflow]

@[grind]
theorem addNsw_assoc_same_sign {n} {hn : Bits n} (x y z : iN n)
    (h :
      (x ≥ₛ 0) &&& (y ≥ₛ 0) &&& (z ≥ₛ 0) ~> 1 ∨
      (x <ₛ 0) &&& (y <ₛ 0) &&& (z <ₛ 0) ~> 1)

    : (x +nsw y) +nsw z <~> x +nsw (y +nsw z) := by

  poison_unroll x y z => a b c
  simp [iN_unwrap_inst] at *

  have h' : a.msb = b.msb ∧ b.msb = c.msb := by
    bv_decide

  rw [BitVec.saddOverflow_chain_assoc_monotone a b c h']
  rw [BitVec.add_assoc a b c]
  exact hn

@[grind]
theorem addNuw_assoc {n} {hn : Bits n} (x y z : iN n)
    : (x +nuw y) +nuw z <~> x +nuw (y +nuw z) := by

  poison_unroll x y z => a b c

  simp [iN_unwrap_inst]
  rw [BitVec.uaddOverflow_chain_assoc a b c]
  rw [BitVec.add_assoc a b c]
  exact hn

end iN
