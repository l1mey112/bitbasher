import theorems.iN

inductive iNBinOp where
  | add
  | addNsw
  | addNuw
  | addNw
deriving Hashable, DecidableEq, Repr

namespace iNBinOp

def eval : iNBinOp → (iN w → iN w → iN w)
  | .add => iN.add
  | .addNsw => iN.addNsw
  | .addNuw => iN.addNuw
  | .addNw => iN.addNw

end iNBinOp

inductive iNExpr : Nat → Type where
  | poison : iNExpr n
  | const : (value : Nat) → iNExpr n
  | input : (idx : Nat) → iNExpr n
  | binop : iNBinOp → iNExpr n → iNExpr n → iNExpr n
with
  @[computed_field]
  hashCode : (n : Nat) → iNExpr n → UInt64
    | n, .poison => mixHash 3 (hash n)
    | n, .input idx => mixHash 5 $ mixHash (hash n) (hash idx)
    | n, .const value => mixHash 7 $ mixHash (hash n) (hash value)
    | n, .binop op lhs rhs => mixHash 11 $ mixHash (hash op) $ mixHash (lhs.hashCode) (rhs.hashCode)
deriving DecidableEq, Repr, Inhabited

instance : Hashable $ iNExpr n where
  hash n := n.hashCode

/- instance decEq : DecidableEq (iNExpr n) := fun l r =>
  withPtrEqDecEq l r fun _ =>
    if h : hash l ≠ hash r then
      .isFalse (ne_of_apply_ne hash h)
    else
      ... -/

namespace iNExpr

structure PackediN where
  n : Nat
  expr : iN n

abbrev Assignment := Lean.RArray PackediN

def Assignment.get (assign : Assignment) (idx : Nat) : PackediN :=
  Lean.RArray.get assign idx

def eval (assign : Assignment) : iNExpr n → iN n
  | .const v => iN.bitvec v
  | .input idx =>
    let pack := assign.get idx
    if h : pack.n = n then
      h ▸ pack.expr
    else
      panic! "type mismatch {pack.n} != {n}"
  | .binop op lhs rhs => (op.eval) (eval assign lhs) (eval assign rhs)
  | .poison => iN.poison

end iNExpr
