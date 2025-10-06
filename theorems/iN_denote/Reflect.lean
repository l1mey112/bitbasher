import theorems.iN
import theorems.iN_denote.iNExpr
import Lean

open Lean Elab Meta

structure Atom where
  width : Nat
  idx : Nat

structure ReifyState where
  /-- Atoms/variables encountered so far. Map from `iN` expression to `(width, idx)` pair. -/
  atoms : Std.HashMap Expr Atom := {}
deriving Inhabited

structure ReifiediNExpr where
  width : Nat
  expr : iNExpr width

abbrev M := StateRefT ReifyState MetaM

namespace M

def run (m : M α) : MetaM α :=
  m.run' {}

end M

/- partial def RuleExpr.of (reducedExpr : Expr) : M ReifiediNExpr := do
  go reducedExpr
where
  go (expr : Expr) : M ReifiediNExpr := do
    match_expr expr with
    | -/

-- TODO figure out how atoms are going to work
