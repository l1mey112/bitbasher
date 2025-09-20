import theorems.iN.iN

@[simp_iN]
def popcount {n} (a : BitVec n) : BitVec n :=
  n.fold (init := 0) fun i _ pop =>
    pop + ((a >>> i) &&& 1)

@[simp_iN]
def popcount? {n} (a : BitVec n) : iN n :=
  bitvec (popcount a)

@[simp_iN]
def llvm_ctpop (x : iN n) := iN.pBind x popcount?

@[simp_iN]
def popcount_p82_hd (x : iN 32) : iN 32 :=
  let x := x - ((x >>>ᵤ 1) &&& 0x55555555)
  let x := (x &&& 0x33333333) + ((x >>>ᵤ 2) &&& 0x33333333)
  let x := (x + (x >>>ᵤ 4)) &&& 0x0F0F0F0F
  let x := x + (x >>>ᵤ 8)
  let x := x + (x >>>ᵤ 16)
  let x := x &&& 0x0000003F
  x

-- https://lean-lang.org/doc/reference/latest/Basic-Types/Bitvectors/?terms=popcount#BitVec-automation
theorem test32 (x : iN 32) : popcount_p82_hd x <~> llvm_ctpop x := by blast
