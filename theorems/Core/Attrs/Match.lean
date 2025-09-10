import Lean

structure Match where

deriving Lean.ToJson, Lean.FromJson, Inhabited



/- structure Match where
  rewrite
deriving Lean.ToJson, Lean.FromJson, Inhabited -/

inductive ExprType : Type where
  | bits : Nat → ExprType
  | bitsOrPoison : Nat → ExprType
  | poison : ExprType

/- inductive Expr : Type where
  | hole : (type : ExprType) → Expr
  | poison : (type : ExprType) → Expr
  /-- Binops -/
  | add : Expr type → Expr type → Expr type
  | sub : Expr type → Expr type → Expr type
  | const : Nat → Expr bits -/
