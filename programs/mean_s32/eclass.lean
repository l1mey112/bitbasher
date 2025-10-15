import theorems.iN
import theorems.ideal

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

--  (no_index (OfNat.ofNat val) : iN n) = iN.bitvec (BitVec.ofNat n val) := rfl

/- @[opt ideal]
theorem t {n val} : x - (no_index (OfNat.ofNat val) : iN n) ~> x + (-val) := -/

/- use optprocs for this -/

-- a - immediate => a + -immediate
-- (a + con1) - (b + con2) => (a - b) + (con1 - con2)

/- // commutativity opts (we want a canonical form).
        int ap = node_pos(a);
        int bp = node_pos(b);
        if (ap < bp || (ap == bp && a->gvn > b->gvn)) {
            set_input(f, n, b, 1);
            set_input(f, n, a, 2);
            return n;
        } -/

-- 1 ≤ x ∧ x ≤ 2

#eval getOptDecls

#check ForIn

example {n} (x : iN n) : x + 0 + 0 + 0 + 0 + 0 ~> x := by
  simp
