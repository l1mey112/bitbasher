import theorems.iN.SimpSets

/--
LLVM-style integers with poison value.
-/
inductive iN (bits : Nat) : Type where
  | bitvec : BitVec bits → iN bits
  | poison : iN bits

export iN (poison bitvec)

instance : OfNat (iN n) val where
  ofNat := iN.bitvec (BitVec.ofNat n val)

instance : Coe Bool (iN 1) where
  coe b := bif b then iN.bitvec 1 else iN.bitvec 0

instance : Coe (BitVec n) (iN n) where
  coe b := iN.bitvec b

instance : Inhabited (iN n) where
  default := poison

namespace iN

@[simp]
theorem ofNat_eq_bitvec_ofNat {n val} :
  (no_index (OfNat.ofNat val) : iN n) = iN.bitvec (BitVec.ofNat n val) := rfl

@[simp, grind =]
theorem bitvec_inj {n} {a b : BitVec n} :
    @Eq (no_index _) (bitvec a) (bitvec b) ↔ a = b := by
  --  ((bitvec a : iN n) = (bitvec b : iN n)) ↔ a = b := by

  constructor
  · intro h
    injection h
  . intro h
    rw [h]

@[simp]
theorem poison_ne_bitvec {n} {a : BitVec n} :
    @Ne (no_index _) (poison) (bitvec a) := by
  --  (poison : iN n) ≠ (bitvec a : iN n) := by

  intro h
  cases h

@[simp]
theorem bitvec_ne_poison {n} {a : BitVec n} :
    @Ne (no_index _) (bitvec a) (poison) := by
  --  (bitvec a : iN n) ≠ (poison : iN n) := by

  intro h
  cases h

@[simp]
theorem ite_bitvec_bitvec {n} {c : Prop} [Decidable c] {a b : BitVec n} :
    (if c then bitvec a else bitvec b : no_index _) = bitvec (if c then a else b) := by
  split <;> rfl

@[simp]
theorem cond_bitvec_bitvec {n} (c : Bool) (t e : BitVec n) :
    cond c (bitvec t) (bitvec e) = bitvec (cond c t e) := by
  cases c <;> rfl

/-
Because `iN` is not a monad, we don't have access to nice `>>=` notation.
-/

def pBind {n m} (x : iN n) (f : BitVec n → iN m) : iN m :=
  match x with
  | poison => poison
  | bitvec a => f a

def pBind₂ {n m k} (x : iN n) (y : iN m) (f : BitVec n → BitVec m → iN k) : iN k :=
  pBind x (fun a => pBind y (fun b => f a b))

@[simp]
theorem poison_pBind {n m} {f : BitVec n → iN m} :
  pBind poison f = poison := rfl

@[simp]
theorem bitvec_pBind {n m} {a : BitVec n} {f : BitVec n → iN m} :
  pBind (bitvec a) f = f a := rfl

@[simp]
theorem pBind_poison {n m} {x : iN n} : pBind x (fun _ => (poison : iN m)) = poison := by
  cases x <;> rfl

@[simp]
theorem pBind_if_then_poison_eq_ite_pBind {n m} {c : Prop} [Decidable c] {x : iN n} {f : BitVec n → iN m} :
    pBind (if c then poison else x : no_index _) f = if c then poison else pBind x f := by
  split <;> rfl

@[simp]
theorem pBind_if_else_poison_eq_ite_pBind {n m} {c : Prop} [Decidable c] {x : iN n} {f : BitVec n → iN m} :
    pBind (if c then x else poison : no_index _) f = if c then pBind x f else poison := by
  split <;> rfl

@[simp]
theorem pBind_cond_poison_left_eq_cond_pBind {n m} {c : Bool} {x : iN n} {f : BitVec n → iN m} :
    pBind (cond c poison x) f = cond c poison (pBind x f) := by
  cases c <;> rfl

@[simp]
theorem pBind_cond_poison_right_eq_cond_pBind {n m} {c : Bool} {x : iN n} {f : BitVec n → iN m} :
    pBind (cond c x poison) f = cond c (pBind x f) poison := by
  cases c <;> rfl

@[simp]
theorem pBind₂_poison_left {n m k} {y : iN m} {f : BitVec n → BitVec m → iN k} :
  pBind₂ poison y f = poison := rfl

@[simp]
theorem pBind₂_poison_right {n m k} {x : iN n} {f : BitVec n → BitVec m → iN k} :
    pBind₂ x poison f = poison := by
  cases x <;> rfl

@[simp]
theorem pBind₂_bitvec_left {n m k} {a : BitVec n} {y : iN m} {f : BitVec n → BitVec m → iN k} :
    pBind₂ (bitvec a) y f = pBind y (fun b => f a b) := rfl

@[simp]
theorem pBind₂_bitvec_right {n m k} {x : iN n} {b : BitVec m} {f : BitVec n → BitVec m → iN k} :
    pBind₂ x (bitvec b) f = pBind x (fun a => f a b) := by
  cases x <;> rfl

@[simp]
theorem pBind₂_bitvec_bitvec {n m k} {a : BitVec n} {b : BitVec m} {f : BitVec n → BitVec m → iN k} :
    pBind₂ (bitvec a) (bitvec b) f = f a b := rfl

@[simp]
theorem pBind₂_if_then_poison_eq_ite_pBind₂ {n m k} {c : Prop} [Decidable c] {x : iN n} {y : iN m} {f : BitVec n → BitVec m → iN k} :
    pBind₂ (if c then poison else x : no_index _) y f = if c then poison else pBind₂ x y f := by
  split <;> rfl

@[simp]
theorem pBind₂_if_else_poison_eq_ite_pBind₂ {n m k} {c : Prop} [Decidable c] {x : iN n} {y : iN m} {f : BitVec n → BitVec m → iN k} :
    pBind₂ (if c then x else poison : no_index _) y f = if c then pBind₂ x y f else poison := by
  split <;> rfl

@[simp]
theorem pBind₂_if_then_poison_right_eq_ite_pBind₂ {n m k} {c : Prop} [Decidable c] {x : iN n} {y : iN m} {f : BitVec n → BitVec m → iN k} :
    pBind₂ x (if c then poison else y : no_index _) f = if c then poison else pBind₂ x y f := by
  split <;> simp

@[simp]
theorem pBind₂_if_else_poison_right_eq_ite_pBind₂ {n m k} {c : Prop} [Decidable c] {x : iN n} {y : iN m} {f : BitVec n → BitVec m → iN k} :
    pBind₂ x (if c then y else poison : no_index _) f = if c then pBind₂ x y f else poison := by
  split <;> simp

@[simp]
theorem pBind₂_cond_poison_left_eq_cond_pBind₂ {n m k} {c : Bool} {x : iN n} {y : iN m} {f : BitVec n → BitVec m → iN k} :
    pBind₂ (cond c poison x) y f = cond c poison (pBind₂ x y f) := by
  cases c <;> rfl

@[simp]
theorem pBind₂_cond_poison_right_eq_cond_pBind₂ {n m k} {c : Bool} {x : iN n} {y : iN m} {f : BitVec n → BitVec m → iN k} :
    pBind₂ x (cond c poison y) f = cond c poison (pBind₂ x y f) := by
  cases c <;> simp

@[simp]
theorem pBind₂_cond_poison_both_eq_cond_pBind₂ {n m k} {c : Bool} {x : iN n} {y : iN m} {f : BitVec n → BitVec m → iN k} :
    pBind₂ (cond c poison x) (cond c poison y) f = cond c poison (pBind₂ x y f) := by
  cases c <;> simp

@[grind =]
theorem pBind₂_comm {n m k} {x : iN n} {y : iN m} {f : BitVec n → BitVec m → iN k} :
    pBind₂ x y f = pBind₂ y x (fun b a => f a b) := by
  cases x <;> cases y <;> rfl

@[simp, grind]
theorem pBind_assoc {n m k} {x : iN n}
    {f : BitVec n → iN m} {g : BitVec m → iN k} :
    pBind (pBind x f) g = pBind x (fun a => pBind (f a) g) := by

  cases x <;> rfl

@[simp]
theorem pBind_if_then_poison_eq_if_pBind {n m} {c : Prop} [Decidable c] {x : iN n} {f : BitVec n → iN m} :
    pBind (if c then poison else x : no_index _) f = if c then poison else pBind x f := by
  split <;> rfl

@[simp]
theorem pBind_if_else_poison_eq_if_pBind {n m} {c : Prop} [Decidable c] {x : iN n} {f : BitVec n → iN m} :
    pBind (if c then x else poison : no_index _) f = if c then pBind x f else poison := by
  split <;> rfl

end iN
