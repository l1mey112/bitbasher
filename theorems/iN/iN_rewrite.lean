import theorems.iN.iN_def

/--
`Rewrite x y` means the value `x` can be rewritten into the value `y`.
-/
inductive Rewrite {n} : iN n → iN n → Prop where
  /-- A non-poison value rewrites to itself. -/
  | bv_refl (v : BitVec n) : Rewrite (bitvec v) (bitvec v)
  /-- Poison can be rewritten into any value. -/
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

/- theorem rewrite_bitvec_iff_equal {n} {x y : BitVec n}
    : (bitvec x <~> bitvec y) ↔ (x = y) := by

  constructor
  case mp =>
    intro h
    cases h with
    | intro hxy hyx =>
      cases hxy
      cases hyx
      rfl
  case mpr =>
    intro h
    rw [h]
    constructor
    case left => exact Rewrite.bv_refl y
    case right => exact Rewrite.bv_refl y -/

-- you can have `poison ~> 12`
