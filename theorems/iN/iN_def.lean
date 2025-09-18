import theorems.iN.SimpSets

/--
LLVM-style integers with poison value.
-/
structure iN (bits : Nat) : Type where
  protected bitvec : BitVec bits
  protected poison : Bool

  protected poison_inv : poison → bitvec = 0

def poison {n : Nat} : iN n := ⟨0, true, by simp⟩
def bitvec {n : Nat} (value : BitVec n) : iN n := ⟨value, false, by simp⟩

abbrev i1 := iN 1
abbrev i8 := iN 8
abbrev i16 := iN 16
abbrev i32 := iN 32
abbrev i64 := iN 64
abbrev i128 := iN 128

instance : OfNat (iN n) val where
  ofNat := bitvec (BitVec.ofNat n val)

instance : Coe Bool (iN 1) where
  coe b := bif b then bitvec 1 else bitvec 0

instance : Coe (BitVec n) (iN n) where
  coe b := bitvec b

@[simp]
theorem ofNat_eq_bitvec_ofNat {n val} :
  (no_index (OfNat.ofNat val) : iN n) = bitvec (BitVec.ofNat n val) := rfl

/-- Macro for matching iN literals in simp-theorems. The normal form that is matched is `iN.ofNat_eq_bitvec`. -/
macro "lit(" val:term ")" : term => `(no_index bitvec (BitVec.ofNat _ $val))

@[simp, grind]
theorem poison_poison {n}
    : (poison : iN n).poison = true := by

  unfold poison
  simp

@[simp, grind]
theorem bitvec_poison {n} (a : BitVec n)
    : (bitvec a).poison = false := by

  unfold bitvec
  simp

@[simp, grind]
theorem bitvec_bitvec {n} (a : BitVec n)
    : (bitvec a).bitvec = a := by

  unfold bitvec
  simp

@[simp, grind]
theorem poison_norm {n} (x : iN n) {h : x.poison = true}
    : x = poison := by

  obtain ⟨x_bitvec, is_poison, poison_inv⟩ := x
  have h' : x_bitvec = 0 := poison_inv h

  subst h'
  subst h
  rfl

@[simp, grind]
theorem bitvec_eq {n} (x : iN n) {h : ¬x.poison = true}
    : bitvec x.bitvec = x := by

  obtain ⟨x_bitvec, is_poison, poison_inv⟩ := x
  unfold bitvec
  simp [*] at *
  exact h

-- normalisation like this isn't the right way to go as,
-- you force unwrapping of structures using `obtain`.

/- @[simp]
theorem bitvec_norm {n} (x : iN n) (a : BitVec n)
    {h : ¬x.poison = true}
    {ha : x.bitvec = a}
    : x = bitvec a := by

  obtain ⟨x_bitvec, _, _⟩ := x
  simp at ha
  simp at h
  simp only [bitvec, iN.mk.injEq]
  exact And.intro ha h -/

-- if at any point, you access `poison.bitvec`, this is an error
-- from the definitions. this should never be reached

protected def iN.poisonWrapper {n} {k} (g : BitVec n → BitVec n → iN k) (x y : iN n) : iN k :=
  if x.poison ∨ y.poison then
    poison
  else
    g x.bitvec y.bitvec

protected def iN.poisonPreconditions {n}
    (isPoison : BitVec n → BitVec n → Bool) (g : BitVec n → BitVec n → BitVec n)
    (a b : BitVec n) : iN n :=

  if isPoison a b then poison else bitvec (g a b)

/--
Equality between two `iN` values, returning an `iN 1` (boolean) result.

LangRef: https://llvm.org/docs/LangRef.html#icmp-instruction
-/
@[iN_unwrap_inst]
protected def iN.icmpEq {n} : iN n → iN n → iN 1 :=
  iN.poisonWrapper (· == ·)

/--
LangRef: https://llvm.org/docs/LangRef.html#icmp-instruction
-/
@[iN_unwrap_inst]
protected def iN.icmpNe {n} : iN n → iN n → iN 1 :=
  iN.poisonWrapper (fun x1 x2 => decide (x1 != x2))

/--
LangRef: https://llvm.org/docs/LangRef.html#icmp-instruction
-/
@[iN_unwrap_inst]
protected def iN.icmpUlt {n} : iN n → iN n → iN 1 :=
  iN.poisonWrapper (fun x1 x2 => decide (x1.toNat < x2.toNat))

/--
LangRef: https://llvm.org/docs/LangRef.html#icmp-instruction
-/
@[iN_unwrap_inst]
protected def iN.icmpUle {n} : iN n → iN n → iN 1 :=
  iN.poisonWrapper (fun x1 x2 => decide (x1 ≤ x2))

/--
LangRef: https://llvm.org/docs/LangRef.html#icmp-instruction
-/
@[iN_unwrap_inst]
protected def iN.icmpUgt {n} : iN n → iN n → iN 1 :=
  iN.poisonWrapper (fun x1 x2 => decide (x1 > x2))

/--
LangRef: https://llvm.org/docs/LangRef.html#icmp-instruction
-/
@[iN_unwrap_inst]
protected def iN.icmpUge {n} : iN n → iN n → iN 1 :=
  iN.poisonWrapper (fun x1 x2 => decide (x1 ≥ x2))

/--
LangRef: https://llvm.org/docs/LangRef.html#icmp-instruction
-/
@[iN_unwrap_inst]
protected def iN.icmpSlt {n} : iN n → iN n → iN 1 :=
  iN.poisonWrapper (fun x1 x2 => x1.slt x2)

/--
LangRef: https://llvm.org/docs/LangRef.html#icmp-instruction
-/
@[iN_unwrap_inst]
protected def iN.icmpSle {n} : iN n → iN n → iN 1 :=
  iN.poisonWrapper (fun x1 x2 => x1.sle x2)

/--
LangRef: https://llvm.org/docs/LangRef.html#icmp-instruction
-/
@[iN_unwrap_inst]
protected def iN.icmpSgt {n} : iN n → iN n → iN 1 :=
  iN.poisonWrapper (fun x1 x2 => !x1.sle x2)

/--
LangRef: https://llvm.org/docs/LangRef.html#icmp-instruction
-/
@[iN_unwrap_inst]
protected def iN.icmpSge {n} : iN n → iN n → iN 1 :=
  iN.poisonWrapper (fun x1 x2 => !x1.slt x2)

@[inherit_doc] infixl:55 " ==ᵤ " => iN.icmpEq
@[inherit_doc] infixl:55 " !=ᵤ " => iN.icmpNe
@[inherit_doc] infixl:55 " <ᵤ "  => iN.icmpUlt
@[inherit_doc] infixl:55 " ≤ᵤ "  => iN.icmpUle
@[inherit_doc] infixl:55 " >ᵤ "  => iN.icmpUgt
@[inherit_doc] infixl:55 " ≥ᵤ "  => iN.icmpUge
@[inherit_doc] infixl:55 " <ₛ "  => iN.icmpSlt
@[inherit_doc] infixl:55 " ≤ₛ "  => iN.icmpSle
@[inherit_doc] infixl:55 " >ₛ "  => iN.icmpSgt
@[inherit_doc] infixl:55 " ≥ₛ "  => iN.icmpSge

/--
LangRef: https://llvm.org/docs/LangRef.html#and-instruction
-/
@[iN_unwrap_inst]
protected def iN.and {n} : iN n → iN n → iN n :=
  iN.poisonWrapper (· &&& ·)

/--
LangRef: https://llvm.org/docs/LangRef.html#or-instruction
-/
@[iN_unwrap_inst]
protected def iN.or {n} : iN n → iN n → iN n :=
  iN.poisonWrapper (· ||| ·)

instance {n} : HAnd (iN n) (iN n) (iN n) where
  hAnd := iN.and

instance {n} : HOr (iN n) (iN n) (iN n) where
  hOr := iN.or

@[iN_unwrap_inst]
protected def iN.addBV {n : Nat} (a b : BitVec n) : iN n :=
  bitvec (a + b)

/--
The integer sum of both operands. If the sum overflows, the result is returned modulo 2ⁿ.

LangRef: https://llvm.org/docs/LangRef.html#add-instruction
-/
@[iN_unwrap_inst]
protected def iN.add {n} : iN n → iN n → iN n :=
  iN.poisonWrapper iN.addBV

@[iN_unwrap_inst]
protected def iN.addNswBV {n : Nat} (a b : BitVec n) : iN n :=
  iN.poisonPreconditions BitVec.saddOverflow (· + ·) a b

/--
The integer sum of both operands. If the signed sum overflows, poison is returned.

LangRef: https://llvm.org/docs/LangRef.html#add-instruction
-/
@[iN_unwrap_inst]
protected def iN.addNsw {n} : iN n → iN n → iN n :=
  iN.poisonWrapper iN.addNswBV

@[iN_unwrap_inst]
protected def iN.addNuwBV {n : Nat} (a b : BitVec n) : iN n :=
  iN.poisonPreconditions BitVec.uaddOverflow (· + ·) a b

/--
The integer sum of both operands. If the unsigned sum overflows, poison is returned.

LangRef: https://llvm.org/docs/LangRef.html#add-instruction
-/
@[iN_unwrap_inst]
protected def iN.addNuw {n} : iN n → iN n → iN n :=
  iN.poisonWrapper iN.addNuwBV

@[iN_unwrap_inst]
protected def iN.addNwBV {n : Nat} (a b : BitVec n) : iN n :=
  let isPoison := fun x y => BitVec.saddOverflow x y || BitVec.uaddOverflow x y
  iN.poisonPreconditions isPoison (· + ·) a b

/--
The integer sum of both operands. If the sum overflows, poison is returned. Equivalent to `add nsw nuw`.

LangRef: https://llvm.org/docs/LangRef.html#add-instruction
-/
@[iN_unwrap_inst]
protected def iN.addNw {n} : iN n → iN n → iN n :=
  iN.poisonWrapper iN.addNwBV

instance : Add (iN n) where
  add := iN.add

@[inherit_doc] infixl:65 " +nsw " => iN.addNsw
@[inherit_doc] infixl:65 " +nuw " => iN.addNuw
@[inherit_doc] infixl:65 " +nw "  => iN.addNw

/- /--
The integer difference of both operands. If the difference overflows, the result is returned modulo 2ⁿ.

LangRef: https://llvm.org/docs/LangRef.html#sub-instruction
-/
@[iN_unwrap_inst]
protected def iN.sub {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => bitvec (a - b)

@[iN_unwrap_inst]
protected def iN.subNswBV {n : Nat} (a b : BitVec n) : iN n :=
  if BitVec.ssubOverflow a b then
    poison
  else
    bitvec (a - b)

/--
The integer difference of both operands. If the signed difference overflows, poison is returned.

LangRef: https://llvm.org/docs/LangRef.html#sub-instruction
-/
@[iN_unwrap_inst]
protected def iN.subNsw {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => iN.subNswBV a b

@[iN_unwrap_inst]
protected def iN.subNuwBV {n : Nat} (a b : BitVec n) : iN n :=
  if BitVec.usubOverflow a b then
    poison
  else
    bitvec (a - b)

/--
The integer difference of both operands. If the unsigned difference overflows, poison is returned.

LangRef: https://llvm.org/docs/LangRef.html#sub-instruction
-/
@[iN_unwrap_inst]
protected def iN.subNuw {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => iN.subNuwBV a b

@[iN_unwrap_inst]
protected def iN.subNwBV {n : Nat} (a b : BitVec n) : iN n :=
  if BitVec.ssubOverflow a b || BitVec.usubOverflow a b then
    poison
  else
    bitvec (a - b)

/--
The integer difference of both operands. If the difference overflows, poison is returned. Equivalent to `sub nsw nuw`.

LangRef: https://llvm.org/docs/LangRef.html#sub-instruction
-/
@[iN_unwrap_inst]
protected def iN.subNw {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => iN.subNwBV a b

instance : Sub (iN n) where
  sub := iN.sub

@[inherit_doc] infixl:65 " -nsw " => iN.subNsw
@[inherit_doc] infixl:65 " -nuw " => iN.subNuw
@[inherit_doc] infixl:65 " -nw "  => iN.subNw -/

/- @[iN_unwrap_inst]
protected def iN.sub {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => a - b

@[iN_unwrap_inst]
protected def iN.sub_nsw {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b =>
    if BitVec.ssubOverflow a b then
      poison
    else
      a - b

@[iN_unwrap_inst]
protected def iN.sub_nuw {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b =>
    if BitVec.usubOverflow a b then
      poison
    else
      a - b -/

/- @[iN_unwrap_inst]
protected def iN.mul {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => a * b

@[iN_unwrap_inst]
protected def iN.mul_nsw {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b =>
    if BitVec.smulOverflow a b then
      poison
    else
      a * b

@[iN_unwrap_inst]
protected def iN.mul_nuw {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b =>
    if BitVec.umulOverflow a b then
      poison
    else
      a * b

@[iN_unwrap_inst]
protected def iN.mul_nw {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b =>
    if BitVec.smulOverflow a b || BitVec.umulOverflow a b then
      poison
    else
      a * b

@[iN_unwrap_inst]
protected def iN.udiv {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b =>
    if n = 0 then
      0
    else if b == 0 then
      poison
    else
      a / b

@[iN_unwrap_inst]
protected def iN.sdiv {n} {z : n != 0} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b =>
    have _ := z
    if b == 0 || (a == BitVec.intMin n && b == -1) then
      poison
    else
      a.sdiv b

/-- Division by `0` in `iN 0` is defined to be `0`, not poison.  -/
@[iN_unwrap_inst]
protected def iN.udiv_exact {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b =>
    if n = 0 then
      0
    else if b == 0 || a % b != 0 then
      poison
    else
      a / b

/-- Division by `0` in `iN 0` is defined to be `0`, not poison.  -/
@[iN_unwrap_inst]
protected def iN.sdiv_exact {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b =>
    if n = 0 then
      0
    else if b == 0 || (a == BitVec.intMin n && b == -1) || a.srem b != 0 then
      poison
    else
      a.sdiv b

/-- Division by `0` in `iN 0` is defined to be `0`, not poison.  -/
@[iN_unwrap_inst]
protected def iN.urem {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b =>
    if n = 0 then
      0
    else if b == 0 then
      poison
    else
      a % b

/-- Division by `0` in `iN 0` is defined to be `0`, not poison.  -/
@[iN_unwrap_inst]
protected def iN.srem {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b =>
    if n = 0 then
      0
    else if b == 0 then
      poison
    else
      a.srem b

@[iN_unwrap_inst]
protected def iN.and {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => a &&& b

@[iN_unwrap_inst]
protected def iN.or {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => a ||| b

@[iN_unwrap_inst]
protected def iN.xor {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => a ^^^ b

@[iN_unwrap_inst]
protected def iN.shl {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b =>
    let s := b.toNat
    if n = 0 then
      0
    else if s >= n then
      poison
    else
      a <<< s
-/

/- @[iN_unwrap_inst]
protected def iN.shlNswClean {n : Nat} (a : BitVec n) (b : BitVec n) : iN n :=
  let s := b.toNat

  if s ≥ n then
    poison
  else
    let res := a <<< s
    -- does the sign bit of the result differ from the sign bit of the original number?
    if a.msb ≠ res.msb then
      poison
    else
      bitvec res

@[iN_unwrap_inst]
protected def iN.shlNsw {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => iN.shlNswClean a b -/

section norm_eqs
/-! These simp-lemmas rewrite the iN operations into equivalent notation -/
@[grind =] theorem icmpEq_eq (x y : iN n) : iN.icmpEq x y = (x ==ᵤ y) := rfl
@[grind =] theorem icmpNe_eq (x y : iN n) : iN.icmpNe x y = (x !=ᵤ y) := rfl
@[grind =] theorem icmpUlt_eq (x y : iN n) : iN.icmpUlt x y = (x <ᵤ y) := rfl
@[grind =] theorem icmpUle_eq (x y : iN n) : iN.icmpUle x y = (x ≤ᵤ y) := rfl
@[grind =] theorem icmpUgt_eq (x y : iN n) : iN.icmpUgt x y = (x >ᵤ y) := rfl
@[grind =] theorem icmpUge_eq (x y : iN n) : iN.icmpUge x y = (x ≥ᵤ y) := rfl
@[grind =] theorem icmpSlt_eq (x y : iN n) : iN.icmpSlt x y = (x <ₛ y) := rfl
@[grind =] theorem icmpSle_eq (x y : iN n) : iN.icmpSle x y = (x ≤ₛ y) := rfl
@[grind =] theorem icmpSgt_eq (x y : iN n) : iN.icmpSgt x y = (x >ₛ y) := rfl
@[grind =] theorem icmpSge_eq (x y : iN n) : iN.icmpSge x y = (x ≥ₛ y) := rfl
@[grind =] theorem and_eq (x y : iN n) : iN.and x y = x &&& y := rfl
@[grind =] theorem or_eq (x y : iN n) : iN.or x y = x ||| y := rfl
@[grind =] theorem add_eq (x y : iN n) : iN.add x y = x + y := rfl
@[grind =] theorem addNsw_eq (x y : iN n) : iN.addNsw x y = x +nsw y := rfl
@[grind =] theorem addNuw_eq (x y : iN n) : iN.addNuw x y = x +nuw y := rfl
@[grind =] theorem addNw_eq (x y : iN n) : iN.addNw x y = x +nw y := rfl
/- @[simp, grind =] theorem sub_eq (x y : iN n) : iN.sub x y = x - y := rfl
@[simp, grind =] theorem subNsw_eq (x y : iN n) : iN.subNsw x y = x -nsw y := rfl
@[simp, grind =] theorem subNuw_eq (x y : iN n) : iN.subNuw x y = x -nuw y := rfl
@[simp, grind =] theorem subNw_eq (x y : iN n) : iN.subNw x y = x -nw y := rfl -/
end norm_eqs

@[iN_unwrap_inst, grind =] theorem bitvec_addNsw_eq_thing (x y : BitVec n) : (bitvec x) +nsw (bitvec y) = iN.addNswBV x y := rfl

section norm_eqs_to_bitvec
/-! When using iN_unwrap_inst, these simp-lemmas rewrite the notation into back into iN, so they can be lowered -/
@[iN_unwrap_inst, grind =] theorem bitvec_icmpEq_eq (x y : iN n) : (x ==ᵤ y) = iN.icmpEq x y := rfl
@[iN_unwrap_inst, grind =] theorem bitvec_icmpNe_eq (x y : iN n) : (x !=ᵤ y) = iN.icmpNe x y := rfl
@[iN_unwrap_inst, grind =] theorem bitvec_icmpUlt_eq (x y : iN n) : (x <ᵤ y) = iN.icmpUlt x y := rfl
@[iN_unwrap_inst, grind =] theorem bitvec_icmpUle_eq (x y : iN n) : (x ≤ᵤ y) = iN.icmpUle x y := rfl
@[iN_unwrap_inst, grind =] theorem bitvec_icmpUgt_eq (x y : iN n) : (x >ᵤ y) = iN.icmpUgt x y := rfl
@[iN_unwrap_inst, grind =] theorem bitvec_icmpUge_eq (x y : iN n) : (x ≥ᵤ y) = iN.icmpUge x y := rfl
@[iN_unwrap_inst, grind =] theorem bitvec_icmpSlt_eq (x y : iN n) : (x <ₛ y) = iN.icmpSlt x y := rfl
@[iN_unwrap_inst, grind =] theorem bitvec_icmpSle_eq (x y : iN n) : (x ≤ₛ y) = iN.icmpSle x y := rfl
@[iN_unwrap_inst, grind =] theorem bitvec_icmpSgt_eq (x y : iN n) : (x >ₛ y) = iN.icmpSgt x y := rfl
@[iN_unwrap_inst, grind =] theorem bitvec_icmpSge_eq (x y : iN n) : (x ≥ₛ y) = iN.icmpSge x y := rfl
@[iN_unwrap_inst, grind =] theorem bitvec_and_eq (x y : iN n) : x &&& y = iN.and x y := rfl
@[iN_unwrap_inst, grind =] theorem bitvec_or_eq (x y : iN n) : x ||| y = iN.or x y := rfl
@[iN_unwrap_inst, grind =] theorem bitvec_add_eq (x y : iN n) : x + y = iN.add x y := rfl
@[iN_unwrap_inst, grind =] theorem bitvec_addNsw_eq (x y : iN n) : x +nsw y = iN.addNsw x y := rfl
@[iN_unwrap_inst, grind =] theorem bitvec_addNuw_eq (x y : iN n) : x +nuw y = iN.addNuw x y := rfl
@[iN_unwrap_inst, grind =] theorem bitvec_addNw_eq (x y : iN n) : x +nw y = iN.addNw x y := rfl
/- @[iN_unwrap_inst, grind =] theorem bitvec_sub_eq (x y : iN n) : x - y = iN.sub x y := rfl
@[iN_unwrap_inst, grind =] theorem bitvec_subNsw_eq (x y : iN n) : x -nsw y = iN.subNsw x y := rfl
@[iN_unwrap_inst, grind =] theorem bitvec_subNuw_eq (x y : iN n) : x -nuw y = iN.subNuw x y := rfl
@[iN_unwrap_inst, grind =] theorem bitvec_subNw_eq (x y : iN n) : x -nw y = iN.subNw x y := rfl -/
end norm_eqs_to_bitvec
