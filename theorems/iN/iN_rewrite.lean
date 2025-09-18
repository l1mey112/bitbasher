import theorems.iN.iN_def

/--
`Rewrite x y` means the value `x` can be rewritten into the value `y`.
-/
def Rewrite {n : Nat} (x y : iN n) : Prop :=
  /- A value rewrites to itself. -/
  (¬x.poison ∧ ¬y.poison ∧ x.bitvec = y.bitvec) ∨

  /- (or) Poison can be rewritten into anything. -/
  (x.poison)

/--
`RewriteIff x y` means `x` can be rewritten into `y` and `y` can be rewritten into `x`.
-/
abbrev RewriteIff {n} (x y : iN n) := Rewrite x y ∧ Rewrite y x

@[inherit_doc] infix:50 " ~> "  => Rewrite
@[inherit_doc] infix:50 " <~> " => RewriteIff

namespace Rewrite

/-- Poison can be rewritten to anything. -/
@[simp, grind]
theorem rewrite_poison {n} (x : iN n)
    : poison ~> x := by

  simp [Rewrite]

/-- Poison can be rewritten to anything. -/
@[simp, grind]
theorem not_bitvec_poision_rewrite {n} (a : BitVec n)
    : ¬bitvec a ~> poison := by

  simp [Rewrite]

@[refl, simp]
theorem rewrite_refl {n} {x : iN n}
    : x <~> x := by

  simp [Rewrite]

@[refl, simp]
theorem rewrite_refl2 {n} {x : iN n}
    : Rewrite x x ∧ Rewrite x x := by

  -- this handles cases after the `abbrev` is unwrapped
  simp [Rewrite]

@[grind →, simp]
theorem rewrite_trans {n} {x y z : iN n}
    {hx : x ~> y} {hy : y ~> z} : x ~> z := by

  simp [Rewrite] at *
  grind

@[grind]
theorem eq_rewrite {n} {x y : iN n}
    : (x = y) → (x <~> y) := by

  intro h
  rw [h]

@[grind, simp ←]
theorem eq_iff_rewrite_bitvec {n} {a b : BitVec n}
    : (a = b) ↔ (bitvec a <~> bitvec b) := by

  constructor
  case mp =>
    intro h
    rw [h]
  case mpr =>
    intro h
    cases h with
    | intro hab hba =>
      simp [Rewrite] at hab
      exact hab

@[simp, grind]
theorem rewrite_bitvec {n} (a b : BitVec n)
    : (bitvec a ~> bitvec b) ↔ a = b := by

  constructor
  case mp =>
    intro h
    simp [Rewrite] at h
    exact h
  case mpr =>
    intro h
    rw [h]
    simp

end Rewrite
