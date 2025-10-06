import theorems.iN
import theorems.Core.Attrs.Attrs
import Std.Data.HashMap
import Lean

open Lean Elab Meta

/-     | w, .var idx => mixHash 5 <| mixHash (hash w) (hash idx)
    | w, .const val => mixHash 7 <| mixHash (hash w) (hash val)
 -/




instance : LawfulHashable $ iNExpr n where
  hash_eq := by simp

structure iNExprPair where
  n : Nat
  expr : iNExpr n
deriving DecidableEq, Repr

instance : EquivBEq $ iNExprPair where
  rfl := BEq.rfl
  symm := BEq.symm
  trans := BEq.trans

instance : Hashable iNExprPair where
  hash v := v.expr.hashCode


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

-- have iNExpr inside ReifiediNExpr which has a bits field, then dependent typing

-- custom hash functions

/- instance : Hashable ExprConst where
  hash -/

-- use `Sea` linearly

-- the `dedup` hashmap is only entirely for optimisation, but not proofs

-- i don't know to what extent the optimiser will depend on unique representation.

/- semantics wise, it makes no difference, however if you were to actually implement
  a verified optimiser that depends on circular control flow like an actual sea of
  nodes optimiser, this would probably help in proving termination about the worklist
  algorithm.

  though since our optimiser is soley on tree code, who cares!
-/

/- follow sort of similarly to a sea of nodes optimiser though, perform:
peephole
- `compute()`
- `try_as_const()`
- GVN/try existing node
if the node didn't fold to a constant
- `idealise()` (canonicalisation)

note that `compute()` expects the types of the children to be computed already, so
we recurse deeply into children nodes, then compute the type.

since we have that there are no loops in execution, we only need to do this once
and it makes things eaiser.

this would be creating a formally verified compiler
-/

/- compute the "types" where you can, you can feed the "type" of the value into
  a proof to actually perform a rewrite
-/

structure ProofChain where


structure Sea where
  bitwidth : Nat
  /-- Input bitwidths. -/
  inputs : Array Nat
  root : iNExpr bitwidth
  cons : Std.HashMap iNExprPair Unit
deriving Repr

def Sea.fromExprInputs {n} (v : iNExpr n) (inputs : Array Nat) : Sea := Id.run do
  let Cons := Std.HashMap iNExprPair Unit

  let rec insExpr (expr : iNExpr n) : StateM Cons (iNExpr n) := do
    let exprOut ← match expr with
    | .const _ => pure expr
    | .input idx =>
      if h : idx ≥ inputs.size then
        pure $ panic! "should be less"
      else if inputs[idx] != n then
        pure $ panic! "argument type mismatch"
      else
        pure expr
    | .binop op lhs rhs => do
      let lhs := (← insExpr lhs)
      let rhs := (← insExpr rhs)
      pure $ iNExpr.binop op lhs rhs

    let internModify (cons : Cons) : iNExpr n × Cons :=
      let pair : iNExprPair := ⟨n, exprOut⟩

      let cons' := cons.insert pair ()
      let pair' := cons'.getKey pair (by simp [cons'])

      have h : iNExpr pair'.n = iNExpr n := by
        have pair_eq : pair' = pair := by
          unfold pair'
          simp_all
        rw [pair_eq]

      (cast h pair'.expr, cons')

    modifyGet internModify

  let ⟨root, cons⟩ ← (insExpr v).run {}
  return ⟨n, inputs, root, cons⟩

def Sea.fromExpr {n} (v : iNExpr n) : Sea := Sea.fromExprInputs v #[]

def Sea.denote (v : Sea) : MetaM Expr := do
  let binders : Array (Name × Expr) := v.inputs.mapIdx fun n x =>
    let name := s!"%{n}"
    (Name.mkSimple name, (.app (.const ``iN []) $ .lit (.natVal x)))

  let Cons := Std.HashMap iNExprPair Expr

  withLocalDeclsDND binders fun (xs : Array Expr) =>
    let rec insExpr (expr : iNExpr n) : StateT Cons MetaM Unit := do
      let t := (← get)

      sorry

  pure ()

#eval Sea.fromExpr (n := 32) (.binop "add" (.const 2) (.const 2))
