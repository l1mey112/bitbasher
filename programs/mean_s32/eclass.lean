import theorems.iN

import Lean
open Lean Parser Elab Meta Tactic

def root₁ (x y : iN 32) := (x +nsw y) >>>ₛ 1
def root₂ (x y : iN 32) := (x +nsw y) /ₛ 2

#eval (root₁ 100 50)
#eval (root₂ 100 50)

theorem comm (x y : iN 32) : x +nsw y ~> y +nsw x := by
  cases x
  cases y
  all_goals simp [simp_iN]
  bv_decide

theorem rewrite_test₁ (x y : iN 32) : x +nsw y + 1 ~> y +nsw x + 1 := by
  exact Rewrite.congrApp (fun x => x + 1) (by simp [simp_iN]) (comm x y)

theorem rewrite_test₂ (x y : iN 32) : x +nsw y + 1 ~> y +nsw x + 1 := by
  apply_rw comm

/-
partial def elabRoot : Syntax → MetaM Expr
 -/
elab "⟨⟨" func:term "⟩⟩" : term => do
  let func ← Term.elabTerm func none

  dbg_trace func
  return func

def root := ⟨⟨root₁⟩⟩
