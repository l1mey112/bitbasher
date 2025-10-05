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
`RewriteIff x y` means `x` can be rewritten into `y` and `y` can be rewritten into `x`.
-/
def RewriteIff {n} (x y : iN n) := Rewrite x y ∧ Rewrite y x

@[inherit_doc] infix:50 " ~> "  => Rewrite
@[inherit_doc] infix:50 " <~> " => RewriteIff

namespace Rewrite

attribute [refl] Rewrite.refl

/-- Poison can be rewritten to anything. -/
@[simp]
theorem poison_rewrite {n} (x : iN n)
    : poison ~> x := by

  cases x
  case bitvec a =>
    exact Rewrite.poison_forge a
  case poison =>
    exact Rewrite.refl poison

/-- Values cannot be rewritten to poison. -/
@[simp]
theorem not_bitvec_poision_rewrite {n} (a : BitVec n)
    : ¬bitvec a ~> poison := by

  intro h
  cases h

@[simp]
theorem rewrite_poison_iff {n} {x : iN n}
    : (x ~> poison) ↔ (x = poison) := by

  constructor
  case mp =>
    intro h
    cases h
    case refl => rfl
  case mpr =>
    intro h
    rw [h]

@[refl]
theorem rewrite_refl {n} (x : iN n)
    : x <~> x := by

  constructor <;> exact Rewrite.refl x

instance {n} : @Std.Refl (iN n) Rewrite where
  refl := Rewrite.refl

instance {n} : @Std.Refl (iN n) RewriteIff where
  refl := Rewrite.rewrite_refl

@[grind →]
theorem trans {n} {x y z : iN n}
    (hx : x ~> y) (hy : y ~> z) : x ~> z := by

  cases hx
  case refl =>
    exact hy
  case poison_forge v =>
    exact poison_rewrite z

/--
Rewrite congruence. Even though no instruction should be able to "observe" poison, `wf` must still be an assumption.
-/
theorem congrApp {n} (f : iN n → iN n)
    (wf : f poison = poison)
    {a a' : iN n} (h : a ~> a') : f a ~> f a' := by

  cases h
  case refl =>
    exact Rewrite.refl (f a)
  case poison_forge v =>
    rw [wf]
    exact poison_rewrite (f (bitvec v))

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
      cases hab
      cases hba
      rfl

@[simp, grind]
theorem rewrite_bitvec_bitvec {n} (a b : BitVec n)
    : (bitvec a ~> bitvec b) ↔ a = b := by

  constructor
  case mp =>
    intro h
    cases h
    case refl => rfl
  case mpr =>
    intro h
    rw [h]

@[simp, grind]
theorem rewrite_bitvec_iN {n} (a : BitVec n) (y : iN n)
    : (bitvec a ~> y) ↔ y = bitvec a := by

  constructor
  case mp =>
    intro h
    cases h
    case refl => rfl
  case mpr =>
    intro h
    rw [h]

@[simp]
theorem if_then_poison_rewrite_iff {n} (c : Prop) [Decidable c] (x y : iN n)
    : (if c then poison else x : no_index _) ~> y ↔ ¬c → x ~> y := by

  split <;> simp [*]

@[simp]
theorem bitvec_rewrite_if_then_poison_iff {n} (a : BitVec n) (c : Prop) [Decidable c] (y : iN n)
    : bitvec a ~> (if c then poison else y : no_index _) ↔ ¬c ∧ bitvec a ~> y := by

  split <;> simp [*]

@[simp]
theorem if_then_rewrite_if_then_iff {n} (c : Prop) [Decidable c] (x1 x2 y1 y2 : iN n)
    : (if c then x1 else x2 : no_index _) ~> (if c then y1 else y2 : no_index _) ↔
      (c → x1 ~> y1) ∧ (¬c → x2 ~> y2) := by

  split <;> simp [*]

@[simp]
theorem if_then_rewrite_iff {n} (c : Prop) [Decidable c] (x1 x2 y : iN n)
    : (if c then x1 else x2 : no_index _) ~> y ↔
      (c → x1 ~> y) ∧ (¬c → x2 ~> y) := by

  split <;> simp [*]

@[simp]
theorem rewrite_if_then_iff {n} (c : Prop) [Decidable c] (x : iN n) (y1 y2 : iN n)
    : x ~> (if c then y1 else y2 : no_index _) ↔
      (c → x ~> y1) ∧ (¬c → x ~> y2) := by

  split <;> simp [*]

-- recreate the above for RewriteIff
@[simp, grind]
theorem rewrite_iff_bitvec_bitvec {n} (a b : BitVec n)
    : (bitvec a <~> bitvec b) ↔ a = b := by

  constructor
  case mp =>
    intro h
    cases h with
    | intro hab hba =>
      cases hab
      cases hba
      rfl
  case mpr =>
    intro h
    rw [h]

@[simp, grind]
theorem rewrite_iff_bitvec_iN {n} (a : BitVec n) (y : iN n)
    : (bitvec a <~> y) ↔ y = bitvec a := by

  constructor
  case mp =>
    intro h
    cases h with
    | intro hab hba =>
      cases hab
      cases hba
      rfl
  case mpr =>
    intro h
    rw [h]

@[simp]
theorem bitvec_rewrite_iff_if_then_poison_iff {n} (a : BitVec n) (c : Prop) [Decidable c] (y : iN n)
    : bitvec a <~> (if c then poison else y : no_index _) ↔ ¬c ∧ bitvec a ~> y := by

  split <;> simp [*]

@[simp]
theorem if_then_rewrite_iff_if_then_iff {n} (c : Prop) [Decidable c] (x1 x2 y1 y2 : iN n)
    : (if c then x1 else x2 : no_index _) <~> (if c then y1 else y2 : no_index _) ↔
      (c → x1 <~> y1) ∧ (¬c → x2 <~> y2) := by

  split <;> simp [*]

@[simp]
theorem if_then_rewrite_iff_iff {n} (c : Prop) [Decidable c] (x1 x2 y : iN n)
    : (if c then x1 else x2 : no_index _) <~> y ↔
      (c → x1 <~> y) ∧ (¬c → x2 <~> y) := by

  split <;> simp [*]

@[simp]
theorem rewrite_iff_if_then_iff {n} (c : Prop) [Decidable c] (x : iN n) (y1 y2 : iN n)
    : x <~> (if c then y1 else y2 : no_index _) ↔
      (c → x <~> y1) ∧ (¬c → x <~> y2) := by

  split <;> simp [*]

@[simp]
theorem poison_rewrite_iff {n} {x : iN n}
    : (poison <~> x) ↔ (x = poison) := by

  constructor
  case mp =>
    intro h
    cases h
    simp_all
  case mpr =>
    intro h
    rw [h]

@[simp]
theorem rewrite_iff_poison {n} (x : iN n)
    : (x <~> poison) ↔ (x = poison) := by

  constructor
  case mp =>
    intro h
    cases h
    simp_all
  case mpr =>
    intro h
    rw [h]

@[simp]
theorem bitvec_rewrite_poison_iff {n} (a : BitVec n)
    : (bitvec a <~> poison) ↔ False := by

  constructor
  case mp =>
    intro h
    cases h
    simp_all
  case mpr =>
    intro h
    cases h

@[simp]
theorem poison_rewrite_bitvec_iff {n} (a : BitVec n)
    : (poison <~> bitvec a) ↔ False := by

  constructor
  case mp =>
    intro h
    cases h
    simp_all
  case mpr =>
    intro h
    cases h

@[simp]
theorem poison_rewrite_poison_iff {n}
    : ((poison : iN n) <~> poison) := by

  constructor <;> exact Rewrite.refl poison

end Rewrite
