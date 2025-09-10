import theorems.iN.iN_def

/--
`Rewrite x y` means the value `x` can be rewritten into the value `y`.
-/
inductive Rewrite {n} : iN n → iN n → Prop where
  /-- A value rewrites to itself. -/
  | refl (x : iN n) : Rewrite x x
  /-- Poison can be rewritten into any concrete value. -/
  | poison_forge (v : BitVec n) : Rewrite poison (bitvec v)

/--
`RewriteReverse x y` means the value `y` can be rewritten into the value `x`.
-/
abbrev RewriteReverse {n} (x y : iN n) := Rewrite y x

/--
`RewriteIff x y` means `x` can be rewritten into `y` and `y` can be rewritten into `x`.
-/
abbrev RewriteIff {n} (x y : iN n) := Rewrite x y ∧ Rewrite y x

@[inherit_doc] infix:50 " ~> "  => Rewrite
@[inherit_doc] infix:50 " <~ "  => RewriteReverse
@[inherit_doc] infix:50 " <~> " => RewriteIff

/-- Poison can be rewritten to anything. -/
@[simp, grind]
theorem rewrite_poison {n} (x : iN n)
    : poison ~> x := by

  cases x
  case bitvec a =>
    exact Rewrite.poison_forge a
  case poison =>
    exact Rewrite.refl poison

@[refl, simp]
theorem rewrite_refl {n} {x : iN n}
    : x <~> x := by

  constructor <;> exact Rewrite.refl x

@[grind →]
theorem rewrite_trans {n} {x y z : iN n}
    {hx : x ~> y} {hy : y ~> z} : x ~> z := by

  cases hx
  case refl =>
    exact hy
  case poison_forge v =>
    exact rewrite_poison z

@[grind]
theorem eq_rewrite {n} {x y : iN n}
    : (x = y) → (x <~> y) := by

  intro h
  rw [h]
  constructor <;> exact Rewrite.refl y

@[grind]
theorem eq_iff_rewrite_bitvec {n} {a b : BitVec n}
    : (a = b) ↔ (bitvec a <~> bitvec b) := by

  constructor
  case mp =>
    intro h
    rw [h]
    constructor
    case left => exact Rewrite.refl (bitvec b)
    case right => exact Rewrite.refl (bitvec b)
  case mpr =>
    intro h
    cases h with
    | intro hab hba =>
      cases hab
      cases hba
      rfl
