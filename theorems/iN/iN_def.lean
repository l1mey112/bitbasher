import theorems.iN.SimpSets

/--
LLVM-style integers with poison value.
-/
inductive iN (bits : Nat) : Type where
  | bitvec : BitVec bits → iN bits
  | poison : iN bits

/-
There are multiple ways to deal with `BitVec 0`

1. Adjust the definitions of the operators to work on `BitVec n`, but always return
   zero on any operation if involving `BitVec 0`.
    - For example "division by `0` in `iN 0` is defined to be `0`, not poison."
    - This complicates proofs, as you need to consider `poison : BitVec 0`, which
      should never be constructible.
      In automated proofs you can end up with `⊢ poison = 0` goals that it can't dispell.

2. Adjust the definitions, but make poison take in a proof that `bits != 0`, so:
   `poison : (h : bits != 0) → iN bits`
    - This is also complicates every facet of proof writing.

3. Adjust the definitions of the operators to take in `{h : n != 0} → iN n`.
    - This seems okay, as the rewrite rules/matchers can supply `h : n != 0`, and
      it being implicit means that Lean can just infer it.
    - This might be the best to facilitate automated proofs.
-/

export iN (poison bitvec)

abbrev i1 := iN 1
abbrev i8 := iN 8
abbrev i16 := iN 16
abbrev i32 := iN 32
abbrev i64 := iN 64
abbrev i128 := iN 128

instance : OfNat (iN n) val where
  ofNat := iN.bitvec (BitVec.ofNat n val)

/--
Pick a value for poison. If `x` is poison, return `value`. Otherwise return `x`.

LangRef: https://llvm.org/docs/LangRef.html#poison-values
-/
def iN.liftPoison {n} (x value : iN n) : iN n :=
  match x with
  | poison => value
  | _ => x

/- /-- Theorem for normalising the iN literal representation. -/
@[simp]
theorem iN.ofNat_eq_bitvec {n : PNat} (val : Nat) :
  ((no_index OfNat.ofNat val) : iN n) = bitvec (no_index OfNat.ofNat val) := rfl -/

/-- Macro for matching iN literals in simp-theorems. The normal form that is matched is `iN.ofNat_eq_bitvec`. -/
macro "lit(" val:term ")" : term => `(no_index bitvec (BitVec.ofNat _ $val))

macro "ofNat(" n:term ")" : term => `(no_index (OfNat.ofNat $n))



/- @OfNat.ofNat PNat 32  -/

/- BitVec.ofNat (↑32) 2 : BitVec ↑32 -/

/--
The integer sum of both operands. If the sum overflows, the result is returned modulo 2ⁿ.

LangRef: https://llvm.org/docs/LangRef.html#add-instruction
-/
@[iN_to_bitvec]
protected def iN.add {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => bitvec (a + b)

@[iN_to_bitvec]
protected def iN.addNswBV {n : Nat} (a b : BitVec n) : iN n :=
  if BitVec.saddOverflow a b then
    poison
  else
    bitvec (a + b)

/--
The integer sum of both operands. If the signed sum overflows, poison is returned.

LangRef: https://llvm.org/docs/LangRef.html#add-instruction
-/
@[iN_unwrap_poison, iN_to_bitvec]
protected def iN.addNsw {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => iN.addNswBV a b

@[iN_to_bitvec]
protected def iN.addNuwBV {n : Nat} (a b : BitVec n) : iN n :=
  if BitVec.uaddOverflow a b then
    poison
  else
    bitvec (a + b)

/--
The integer sum of both operands. If the unsigned sum overflows, poison is returned.

LangRef: https://llvm.org/docs/LangRef.html#add-instruction
-/
@[iN_unwrap_poison, iN_to_bitvec]
protected def iN.addNuw {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => iN.addNuwBV a b

@[iN_to_bitvec]
protected def iN.addNwBV {n : Nat} (a b : BitVec n) : iN n :=
  if BitVec.saddOverflow a b || BitVec.uaddOverflow a b then
    poison
  else
    bitvec (a + b)

/--
The integer sum of both operands. If the sum overflows, poison is returned. Equivalent to `add nsw nuw`.

LangRef: https://llvm.org/docs/LangRef.html#add-instruction
-/
@[iN_unwrap_poison, iN_to_bitvec]
protected def iN.addNw {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => iN.addNwBV a b

instance : Add (iN n) where
  add := iN.add

@[inherit_doc] infixl:65 " +nsw " => iN.addNsw
@[inherit_doc] infixl:65 " +nuw " => iN.addNuw
@[inherit_doc] infixl:65 " +nw "  => iN.addNw

/--
The integer difference of both operands. If the difference overflows, the result is returned modulo 2ⁿ.

LangRef: https://llvm.org/docs/LangRef.html#sub-instruction
-/
@[iN_to_bitvec]
protected def iN.sub {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => bitvec (a - b)

@[iN_to_bitvec]
protected def iN.subNswBV {n : Nat} (a b : BitVec n) : iN n :=
  if BitVec.ssubOverflow a b then
    poison
  else
    bitvec (a - b)

/--
The integer difference of both operands. If the signed difference overflows, poison is returned.

LangRef: https://llvm.org/docs/LangRef.html#sub-instruction
-/
@[iN_unwrap_poison, iN_to_bitvec]
protected def iN.subNsw {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => iN.subNswBV a b

@[iN_to_bitvec]
protected def iN.subNuwBV {n : Nat} (a b : BitVec n) : iN n :=
  if BitVec.usubOverflow a b then
    poison
  else
    bitvec (a - b)

/--
The integer difference of both operands. If the unsigned difference overflows, poison is returned.

LangRef: https://llvm.org/docs/LangRef.html#sub-instruction
-/
@[iN_unwrap_poison, iN_to_bitvec]
protected def iN.subNuw {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => iN.subNuwBV a b

@[iN_to_bitvec]
protected def iN.subNwBV {n : Nat} (a b : BitVec n) : iN n :=
  if BitVec.ssubOverflow a b || BitVec.usubOverflow a b then
    poison
  else
    bitvec (a - b)

/--
The integer difference of both operands. If the difference overflows, poison is returned. Equivalent to `sub nsw nuw`.

LangRef: https://llvm.org/docs/LangRef.html#sub-instruction
-/
@[iN_unwrap_poison, iN_to_bitvec]
protected def iN.subNw {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => iN.subNwBV a b

instance : Sub (iN n) where
  sub := iN.sub

@[inherit_doc] infixl:65 " -nsw " => iN.subNsw
@[inherit_doc] infixl:65 " -nuw " => iN.subNuw
@[inherit_doc] infixl:65 " -nw "  => iN.subNw

/- @[iN_to_bitvec]
protected def iN.sub {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => a - b

@[iN_to_bitvec]
protected def iN.sub_nsw {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b =>
    if BitVec.ssubOverflow a b then
      poison
    else
      a - b

@[iN_to_bitvec]
protected def iN.sub_nuw {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b =>
    if BitVec.usubOverflow a b then
      poison
    else
      a - b -/

/- @[iN_to_bitvec]
protected def iN.mul {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => a * b

@[iN_to_bitvec]
protected def iN.mul_nsw {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b =>
    if BitVec.smulOverflow a b then
      poison
    else
      a * b

@[iN_to_bitvec]
protected def iN.mul_nuw {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b =>
    if BitVec.umulOverflow a b then
      poison
    else
      a * b

@[iN_to_bitvec]
protected def iN.mul_nw {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b =>
    if BitVec.smulOverflow a b || BitVec.umulOverflow a b then
      poison
    else
      a * b

@[iN_to_bitvec]
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

@[iN_to_bitvec]
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
@[iN_to_bitvec]
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
@[iN_to_bitvec]
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
@[iN_to_bitvec]
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
@[iN_to_bitvec]
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

@[iN_to_bitvec]
protected def iN.and {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => a &&& b

@[iN_to_bitvec]
protected def iN.or {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => a ||| b

@[iN_to_bitvec]
protected def iN.xor {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => a ^^^ b

@[iN_to_bitvec]
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

@[iN_to_bitvec]
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

@[iN_unwrap_poison, iN_to_bitvec]
protected def iN.shlNsw {n} : iN n → iN n → iN n
  | poison, _ => poison
  | _, poison => poison
  | bitvec a, bitvec b => iN.shlNswClean a b

section norm_eqs
/-! These simp-lemmas rewrite the iN operations into equivalent notation -/
@[simp, grind =] theorem add_eq (x y : iN n) : iN.add x y = x + y := rfl
@[simp, grind =] theorem addNsw_eq (x y : iN n) : iN.addNsw x y = x +nsw y := rfl
@[simp, grind =] theorem addNuw_eq (x y : iN n) : iN.addNuw x y = x +nuw y := rfl
@[simp, grind =] theorem addNw_eq (x y : iN n) : iN.addNw x y = x +nw y := rfl
@[simp, grind =] theorem sub_eq (x y : iN n) : iN.sub x y = x - y := rfl
@[simp, grind =] theorem subNsw_eq (x y : iN n) : iN.subNsw x y = x -nsw y := rfl
@[simp, grind =] theorem subNuw_eq (x y : iN n) : iN.subNuw x y = x -nuw y := rfl
@[simp, grind =] theorem subNw_eq (x y : iN n) : iN.subNw x y = x -nw y := rfl
end norm_eqs

section norm_eqs_to_bitvec
/-! When using iN_to_bitvec, these simp-lemmas rewrite the notation into back into iN, so they can be lowered -/
@[iN_to_bitvec, grind =] theorem bitvec_add_eq (x y : iN n) : x + y = iN.add x y := rfl
@[iN_to_bitvec, grind =] theorem bitvec_addNsw_eq (x y : iN n) : x +nsw y = iN.addNsw x y := rfl
@[iN_to_bitvec, grind =] theorem bitvec_addNuw_eq (x y : iN n) : x +nuw y = iN.addNuw x y := rfl
@[iN_to_bitvec, grind =] theorem bitvec_addNw_eq (x y : iN n) : x +nw y = iN.addNw x y := rfl
@[iN_to_bitvec, grind =] theorem bitvec_sub_eq (x y : iN n) : x - y = iN.sub x y := rfl
@[iN_to_bitvec, grind =] theorem bitvec_subNsw_eq (x y : iN n) : x -nsw y = iN.subNsw x y := rfl
@[iN_to_bitvec, grind =] theorem bitvec_subNuw_eq (x y : iN n) : x -nuw y = iN.subNuw x y := rfl
@[iN_to_bitvec, grind =] theorem bitvec_subNw_eq (x y : iN n) : x -nw y = iN.subNw x y := rfl
end norm_eqs_to_bitvec
