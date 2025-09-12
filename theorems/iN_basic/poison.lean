import theorems.iN.iN

theorem poison_forge_12 {n} : (poison : iN n) ~> 12 := by
  exact Rewrite.poison_forge 12

-- you cannot have `12 ~> poison`
theorem no_12_forge_poison {n} : ¬((12 : iN n) ~> poison) := by
  intro h
  cases h
  -- there are no cases in `Rewrite` for `bitvec → poision`

-- hence, `12` and `poison` are not equivalent, so you cannot have `poison <~> 12`
theorem poison_12_not_equivalent {n} : ¬ (poison <~> (12 : iN n)) := by
  intro h
  cases h with
  | intro h1 h2 =>
    exact no_12_forge_poison h2

def UINT32_MAX : BitVec 32 := 2 ^ 32 - 1

-- `UINT32_MAX + 1 == 12` ??
theorem overflow_is_12 :
    (bitvec UINT32_MAX) +nuw 1 ~> (12 : i32) := by

  have h : BitVec.uaddOverflow UINT32_MAX 1 = true := by
    decide

  simp [iN_unwrap_inst, h] at *

def INT32_MAX : BitVec 32 := (2 ^ 31) - 1

-- `INT32_MAX + 1 == 12` ??
theorem signed_overflow_is_12 :
    (bitvec INT32_MAX) +nsw 1 ~> (12 : i32) := by

  have h : BitVec.saddOverflow INT32_MAX 1 = true := by
    decide

  simp [iN_unwrap_inst, h] at *
