import theorems.iN

import Lean
import Qq

open Qq
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

-- given some expr, optimise to expr' with proof that expr ~> expr'
set_option trace.Meta.opti true

def root₁ (x y : iN 32) := x +nsw y
def root := ⟨⟨root₁⟩⟩ -- "optimise" `root₁`

/- basically, the only "optimisation" done right now turns every `x ~> x + 0` -/
example : root = fun x y => x +nsw y := by rfl

theorem opt_works (x y : iN 32) : root₁ x y ~> root x y := by
  opt_showcorrect root₁ root
