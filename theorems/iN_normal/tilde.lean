import theorems.iN.SimpSets
import theorems.iN.iN_def
import theorems.Core.Attrs.Attrs

namespace iN

/- @[rewrite, simp]
theorem const_swap {u} (a b con1 con2 : BitVec u)
    : (a + con1) - (b + con2) = (a - b) + (con1 - con2) := by

    grind -/


-- Lifts a binary operation on BitVecs to iN, handling poison automatically.
def iN.lift₂ {n : PNat} (f : BitVec n → BitVec n → BitVec n) : iN n → iN n → iN n
  | poison,   _      => poison
  | _,        poison => poison
  | bitvec a, bitvec b => bitvec (f a b)

-- Simp lemmas that teach Lean how this function works. This is the "bubbling up" logic.
/- @[simp] theorem iN.lift₂_poison_left {n} (f) (y : iN n) : iN.lift₂ f poison y = poison := rfl

@[simp] theorem iN.lift₂_poison_right {n} (f) (x : iN n) : iN.lift₂ f x poison = poison := by cases x <;> rfl
@[simp] theorem iN.lift₂_bitvec {n} (f) (a b : BitVec n) : iN.lift₂ f (bitvec a) (bitvec b) = bitvec (f a b) := rfl
 -/

@[simp] theorem add_match_eta {n} (x y : iN n) :
  (match x, y with
    | poison, _ => poison
    | _, poison => poison
    | bitvec a, bitvec b => bitvec (a + b)) = x + y := rfl

@[simp] theorem sub_match_eta {n} (x y : iN n) :
  (match x, y with
    | poison, _ => poison
    | _, poison => poison
    | bitvec a, bitvec b => bitvec (a - b)) = x - y := rfl

theorem add_match_eta_lit {n} (x : iN n) (con : Nat) :
  (match x, lit(con) with
    | poison, _ => poison
    | _, poison => poison
    | bitvec a, bitvec b => bitvec (a + b)) = x + lit(con) := rfl

theorem sub_match_eta_lit {n} (x : iN n) (con : Nat) :
  (match x, lit(con) with
    | poison, _ => poison
    | _, poison => poison
    | bitvec a, bitvec b => bitvec (a - b)) = x - lit(con) := rfl

/--  -/
--@[rewrite, simp]
theorem const_swap {n} (x y : iN n) (con1 con2 : Nat)
    : (a + lit(con1)) - (b + lit(con1)) = (a - b) + (lit(con1) - lit(con1)) := by

  simp [iN_to_bitvec, *] at *
    /-
    bits✝ : PNat
    a b : iN bits✝
    n : PNat
    x y : iN n
    con1 con2 : Nat
    ⊢ (match
        match a, bitvec (BitVec.ofNat (↑bits✝) con1) with
        | poison, x => poison
        | x, poison => poison
        | bitvec a, bitvec b => bitvec (a + b),
        match b, bitvec (BitVec.ofNat (↑bits✝) con1) with
        | poison, x => poison
        | x, poison => poison
        | bitvec a, bitvec b => bitvec (a + b) with
      | poison, x => poison
      | x, poison => poison
      | bitvec a, bitvec b => bitvec (a - b)) =
      match
        match a, b with
        | poison, x => poison
        | x, poison => poison
        | bitvec a, bitvec b => bitvec (a - b),
        bitvec 0#↑bits✝ with
      | poison, x => poison
      | x, poison => poison
      | bitvec a, bitvec b => bitvec (a + b)
    -/


end iN
