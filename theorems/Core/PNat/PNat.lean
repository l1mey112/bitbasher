def PNat := { n : Nat // 0 < n } deriving DecidableEq

-- https://github.com/leanprover-community/mathlib4/blob/88928cefd7edb1ba61623bffd4e86389dfe1f648/Mathlib/Data/PNat/Notation.lean#L11-L14

@[coe, simp]
def PNat.val : PNat → Nat := Subtype.val

instance : Coe PNat Nat :=
  ⟨PNat.val⟩

instance : OfNat PNat (n + 1) where
  ofNat := ⟨n + 1, by simp⟩

instance : Repr PNat :=
  ⟨fun n n' => reprPrec n.1 n'⟩

namespace PNat

@[simp]
theorem toNat_norm {n : PNat} : ↑n = n.val := rfl

@[simp]
theorem ne_zero (n : PNat) : ↑n ≠ (0 : Nat) := by
  exact Nat.ne_of_gt n.property

end PNat
