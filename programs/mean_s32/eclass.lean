import theorems.iN

import Lean

open Lean Parser Elab Meta Tactic

def root₂ (x y : iN 32) := (x +nsw y) /ₛ 2

#eval (root₂ 100 50)

theorem comm (x y : iN 32) : x +nsw y ~> y +nsw x := by
  cases x
  cases y
  all_goals simp [simp_iN]
  bv_decide

theorem commw (x y : iN 32) : x + y ~> y + x := by
  cases x
  cases y
  all_goals simp [simp_iN]
  ac_nf

theorem rewrite_test₁ (x y : iN 32) : x +nsw y + 1 ~> y +nsw x + 1 := by
  exact Rewrite.congrApp (fun x => x + 1) (by simp [simp_iN]) (comm x y)

theorem rewrite_test₂ (x y : iN 32) : x +nsw y + 1 ~> y +nsw x + 1 := by
  opt_rw comm

theorem commn (x y : iN n) : x + y ~> y + x := by
  blast

theorem rewrite_test₃ (x y : iN n) : x + y + 1 ~> y + x + 1 := by
  opt_rw commn x y

-- given some expr, optimise to expr' with proof that expr ~> expr'
set_option trace.Meta.opti true

/- @[opt ideal]
theorem add_zero (x : iN 32) : x + 0 ~> x := by
  cases x
  all_goals simp [simp_iN] -/

-- x + 0 ~> x
/- optproc addZero := fun e => do
  let_expr HAdd.hAdd _ _ _ _ p q := e | return none

  if let some (0, _) := (← getOfNatValue? q ``iN) then
    return some { expr := p, proof? := ← mkAppM ``add_zero #[p] }

  return none -/

/- def root₁ (x y : iN 32) := (x +nsw y) + 0 + 0

def root := ⟨⟨root₁⟩⟩ -- "optimise" `root₁`

#print root

example (x y : iN 32) : root₁ x y ~> root x y := by
  opt_showcorrect root₁ root -/


@[opt ideal]
theorem add_zeron {n} (x : iN n) : x + 0 ~> x := by
  cases x
  all_goals simp [simp_iN]

example {n} (x : iN n) : x + 0 + 0 + 0 + 0 + 0 ~> x := by
  opt
