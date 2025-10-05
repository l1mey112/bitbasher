import theorems.iN.SimpSets
import theorems.iN.iN_def

namespace iN

@[simp_iN]
def add? {n} (a b : BitVec n) : iN n := bitvec (a + b)

@[simp_iN]
def add {n} (x y : iN n) : iN n := pBind₂ x y add?

@[simp_iN]
def addNsw? {n} (a b : BitVec n) : iN n :=
  if BitVec.saddOverflow a b then
    poison
  else
    add? a b

@[simp_iN]
def addNsw {n} (x y : iN n) : iN n := pBind₂ x y addNsw?

@[simp_iN]
def addNuw? {n} (a b : BitVec n) : iN n :=
  if BitVec.uaddOverflow a b then
    poison
  else
    add? a b

@[simp_iN]
def addNuw {n} (x y : iN n) : iN n := pBind₂ x y addNuw?

@[simp_iN]
def addNw? {n} (a b : BitVec n) : iN n :=
  if BitVec.saddOverflow a b then
    poison
  else if BitVec.uaddOverflow a b then
    poison
  else
    add? a b

@[simp_iN]
def addNw {n} (x y : iN n) : iN n := pBind₂ x y addNw?

instance : Add (iN n) where
  add := iN.add

infixl:65 " +nsw " => iN.addNsw
infixl:65 " +nuw " => iN.addNuw
infixl:65 " +nw "  => iN.addNw

@[simp_iN]
def sub? {n} (a b : BitVec n) : iN n := bitvec (a - b)

@[simp_iN]
def sub {n} (x y : iN n) : iN n := pBind₂ x y sub?

@[simp_iN]
def subNsw? {n} (a b : BitVec n) : iN n :=
  if BitVec.ssubOverflow a b then
    poison
  else
    sub? a b

@[simp_iN]
def subNsw {n} (x y : iN n) : iN n := pBind₂ x y subNsw?

@[simp_iN]
def subNuw? {n} (a b : BitVec n) : iN n :=
  if BitVec.usubOverflow a b then
    poison
  else
    sub? a b

@[simp_iN]
def subNuw {n} (x y : iN n) : iN n := pBind₂ x y subNuw?

@[simp_iN]
def subNw? {n} (a b : BitVec n) : iN n :=
  if BitVec.ssubOverflow a b then
    poison
  else if BitVec.usubOverflow a b then
    poison
  else
    sub? a b

@[simp_iN]
def subNw {n} (x y : iN n) : iN n := pBind₂ x y subNw?

instance : Sub (iN n) where
  sub := iN.sub

infixl:65 " -nsw " => iN.subNsw
infixl:65 " -nuw " => iN.subNuw
infixl:65 " -nw "  => iN.subNw

@[simp_iN]
def icmpEq? {n} (x y : BitVec n) : iN 1 := bitvec (if x == y then 1 else 0)

@[simp_iN]
def icmpEq {n} (x y : iN n) : iN 1 := pBind₂ x y icmpEq?

@[simp_iN]
def icmpNe? {n} (x y : BitVec n) : iN 1 := bitvec (if x != y then 1 else 0)

@[simp_iN]
def icmpNe {n} (x y : iN n) : iN 1 := pBind₂ x y icmpNe?

@[simp_iN]
def icmpUgt? {n} (x y : BitVec n) : iN 1 := bitvec (if x > y then 1 else 0)

@[simp_iN]
def icmpUgt {n} (x y : iN n) : iN 1 := pBind₂ x y icmpUgt?

@[simp_iN]
def icmpUge? {n} (x y : BitVec n) : iN 1 := bitvec (if x >= y then 1 else 0)

@[simp_iN]
def icmpUge {n} (x y : iN n) : iN 1 := pBind₂ x y icmpUge?

@[simp_iN]
def icmpUlt? {n} (x y : BitVec n) : iN 1 := bitvec (if x < y then 1 else 0)

@[simp_iN]
def icmpUlt {n} (x y : iN n) : iN 1 := pBind₂ x y icmpUlt?

@[simp_iN]
def icmpUle? {n} (x y : BitVec n) : iN 1 := bitvec (if x <= y then 1 else 0)

@[simp_iN]
def icmpUle {n} (x y : iN n) : iN 1 := pBind₂ x y icmpUle?

@[simp_iN]
def icmpSgt? {n} (x y : BitVec n) : iN 1 := bitvec (if x.sle y then 0 else 1) -- inverse

@[simp_iN]
def icmpSgt {n} (x y : iN n) : iN 1 := pBind₂ x y icmpSgt?

@[simp_iN]
def icmpSge? {n} (x y : BitVec n) : iN 1 := bitvec (if x.slt y then 0 else 1) -- inverse

@[simp_iN]
def icmpSge {n} (x y : iN n) : iN 1 := pBind₂ x y icmpSge?

@[simp_iN]
def icmpSlt? {n} (x y : BitVec n) : iN 1 := bitvec (if x.slt y then 1 else 0)

@[simp_iN]
def icmpSlt {n} (x y : iN n) : iN 1 := pBind₂ x y icmpSlt?

@[simp_iN]
def icmpSle? {n} (x y : BitVec n) : iN 1 := bitvec (if x.sle y then 1 else 0)

@[simp_iN]
def icmpSle {n} (x y : iN n) : iN 1 := pBind₂ x y icmpSle?

infixl:55 " ==ᵤ " => iN.icmpEq
infixl:55 " !=ᵤ " => iN.icmpNe
infixl:55 " <ᵤ "  => iN.icmpUlt
infixl:55 " ≤ᵤ "  => iN.icmpUle
infixl:55 " >ᵤ "  => iN.icmpUgt
infixl:55 " ≥ᵤ "  => iN.icmpUge
infixl:55 " <ₛ "  => iN.icmpSlt
infixl:55 " ≤ₛ "  => iN.icmpSle
infixl:55 " >ₛ "  => iN.icmpSgt
infixl:55 " ≥ₛ "  => iN.icmpSge

@[simp_iN]
def and {n} (x y : iN n) : iN n := pBind₂ x y (fun a b => bitvec (a &&& b))

@[simp_iN]
def or {n} (x y : iN n) : iN n := pBind₂ x y (fun a b => bitvec (a ||| b))

@[simp_iN]
def not {n} (x : iN n) : iN n := pBind x (fun a => bitvec (~~~a))

@[simp_iN]
def xor {n} (x y : iN n) : iN n := pBind₂ x y (fun a b => bitvec (a ^^^ b))

instance : HAnd (iN n) (iN n) (iN n) where
  hAnd := iN.and

instance : HOr (iN n) (iN n) (iN n) where
  hOr := iN.or

instance : Complement (iN n) where
  complement := iN.not

instance : HXor (iN n) (iN n) (iN n) where
  hXor := iN.xor

@[simp_iN]
def shl? {n} (a b : BitVec n) : iN n :=
  if n == 0 then
    0
  else if b >= n then
    poison
  else
    bitvec (a <<< b)

@[simp_iN]
def shl {n} (x y : iN n) : iN n := pBind₂ x y shl?

@[simp_iN]
def shlNsw? {n} (a b : BitVec n) : iN n :=
  if n == 0 then
    0
  else if ((a <<< b).sshiftRight' b ≠ a) then
    poison
  else
    shl? a b

@[simp_iN]
def shlNsw {n} (x y : iN n) : iN n := pBind₂ x y shlNsw?

@[simp_iN]
def shlNuw? {n} (a b : BitVec n) : iN n :=
  if n == 0 then
    0
  else if ((a <<< b) >>> b ≠ a) then
    poison
  else
    shl? a b

@[simp_iN]
def shlNuw {n} (x y : iN n) : iN n := pBind₂ x y shlNuw?

instance : HShiftLeft (iN n) (iN n) (iN n) where
  hShiftLeft := iN.shl

infixl:75 " <<<nsw " => iN.shlNsw
infixl:75 " <<<nuw " => iN.shlNuw

@[simp_iN]
def lshr? {n} (a b : BitVec n) : iN n :=
  if n == 0 then
    0
  else if b >= n then
    poison
  else
    bitvec (a >>> b)

@[simp_iN]
def lshr {n} (x y : iN n) : iN n := pBind₂ x y lshr?

@[simp_iN]
def lshrExact? {n} (a b : BitVec n) : iN n :=
  if n == 0 then
    0
  else if b >= n then
    poison
  else if (a <<< b) >>> b ≠ a then
    poison
  else
    lshr? a b

@[simp_iN]
def lshrExact {n} (x y : iN n) : iN n := pBind₂ x y lshrExact?

infixl:75 " >>>ᵤ " => iN.lshr
infixl:75 " >>>ᵤexact " => iN.lshrExact

@[simp_iN]
def ashr? {n} (a b : BitVec n) : iN n :=
  if n == 0 then
    0
  else if b >= n then
    poison
  else
    bitvec (a.sshiftRight' b)

@[simp_iN]
def ashr {n} (x y : iN n) : iN n := pBind₂ x y ashr?

@[simp_iN]
def ashrExact? {n} (a b : BitVec n) : iN n :=
  if n == 0 then
    0
  else if b >= n then
    poison
  else if (a >>> b) <<< b ≠ a then
    poison
  else
    ashr? a b

@[simp_iN]
def ashrExact {n} (x y : iN n) : iN n := pBind₂ x y ashrExact?

infixl:75 " >>>ₛ " => iN.ashr
infixl:75 " >>>ₛexact " => iN.ashrExact

@[simp_iN]
def sdiv? {n} (a b : BitVec n) : iN n :=
  if b == 0 then
    poison
  else if b == -1 && a == BitVec.intMin n then
    poison
  else
    bitvec (a.sdiv b)

@[simp_iN]
def sdiv {n} (x y : iN n) : iN n := pBind₂ x y sdiv?

infixl:70 " /ₛ " => iN.sdiv

end iN

section norm_eqs_simp_iN
/-! When using simp_iN, these simp-lemmas rewrite the notation into back into iN, so they can be lowered -/
@[simp_iN] theorem bitvec_icmpEq_eq (x y : iN n) : (x ==ᵤ y) = iN.icmpEq x y := rfl
@[simp_iN] theorem bitvec_icmpNe_eq (x y : iN n) : (x !=ᵤ y) = iN.icmpNe x y := rfl
@[simp_iN] theorem bitvec_icmpUlt_eq (x y : iN n) : (x <ᵤ y) = iN.icmpUlt x y := rfl
@[simp_iN] theorem bitvec_icmpUle_eq (x y : iN n) : (x ≤ᵤ y) = iN.icmpUle x y := rfl
@[simp_iN] theorem bitvec_icmpUgt_eq (x y : iN n) : (x >ᵤ y) = iN.icmpUgt x y := rfl
@[simp_iN] theorem bitvec_icmpUge_eq (x y : iN n) : (x ≥ᵤ y) = iN.icmpUge x y := rfl
@[simp_iN] theorem bitvec_icmpSlt_eq (x y : iN n) : (x <ₛ y) = iN.icmpSlt x y := rfl
@[simp_iN] theorem bitvec_icmpSle_eq (x y : iN n) : (x ≤ₛ y) = iN.icmpSle x y := rfl
@[simp_iN] theorem bitvec_icmpSgt_eq (x y : iN n) : (x >ₛ y) = iN.icmpSgt x y := rfl
@[simp_iN] theorem bitvec_icmpSge_eq (x y : iN n) : (x ≥ₛ y) = iN.icmpSge x y := rfl
@[simp_iN] theorem bitvec_and_eq (x y : iN n) : x &&& y = iN.and x y := rfl
@[simp_iN] theorem bitvec_or_eq (x y : iN n) : x ||| y = iN.or x y := rfl
@[simp_iN] theorem bitvec_add_eq (x y : iN n) : x + y = iN.add x y := rfl
@[simp_iN] theorem bitvec_addNsw_eq (x y : iN n) : x +nsw y = iN.addNsw x y := rfl
@[simp_iN] theorem bitvec_addNuw_eq (x y : iN n) : x +nuw y = iN.addNuw x y := rfl
@[simp_iN] theorem bitvec_addNw_eq (x y : iN n) : x +nw y = iN.addNw x y := rfl
@[simp_iN] theorem bitvec_sub_eq (x y : iN n) : x - y = iN.sub x y := rfl
@[simp_iN] theorem bitvec_subNsw_eq (x y : iN n) : x -nsw y = iN.subNsw x y := rfl
@[simp_iN] theorem bitvec_subNuw_eq (x y : iN n) : x -nuw y = iN.subNuw x y := rfl
@[simp_iN] theorem bitvec_subNw_eq (x y : iN n) : x -nw y = iN.subNw x y := rfl
@[simp_iN] theorem bitvec_not_eq (x : iN n) : ~~~x = iN.not x := rfl
@[simp_iN] theorem bitvec_xor_eq (x y : iN n) : x ^^^ y = iN.xor x y := rfl
@[simp_iN] theorem bitvec_shl_eq (x y : iN n) : x <<< y = iN.shl x y := rfl
@[simp_iN] theorem bitvec_shlNsw_eq (x y : iN n) : x <<<nsw y = iN.shlNsw x y := rfl
@[simp_iN] theorem bitvec_shlNuw_eq (x y : iN n) : x <<<nuw y = iN.shlNuw x y := rfl
@[simp_iN] theorem bitvec_lshr_eq (x y : iN n) : x >>>ᵤ y = iN.lshr x y := rfl
@[simp_iN] theorem bitvec_lshrExact_eq (x y : iN n) : x >>>ᵤexact y = iN.lshrExact x y := rfl
@[simp_iN] theorem bitvec_ashr_eq (x y : iN n) : x >>>ₛ y = iN.ashr x y := rfl
@[simp_iN] theorem bitvec_ashrExact_eq (x y : iN n) : x >>>ₛexact y = iN.ashrExact x y := rfl
@[simp_iN] theorem bitvec_sdiv_eq (x y : iN n) : x /ₛ y = iN.sdiv x y := rfl
end norm_eqs_simp_iN
