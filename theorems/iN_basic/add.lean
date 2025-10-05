import theorems.iN

namespace iN

@[rule]
theorem add_comm (x y : iN n)
    : x + y <~> y + x := by blast

@[rule]
theorem addNsw_comm (x y : iN n)
    : x +nsw y <~> y +nsw x := by blast

@[rule]
theorem addNuw_comm (x y : iN n)
    : x +nuw y <~> y +nuw x := by blast

@[rule]
theorem addNw_comm (x y : iN n)
    : x +nw y <~> y +nw x := by blast

@[rule]
theorem addNsw_refine (x y : iN n)
  : x +nsw y ~> x + y := by blast

@[rule]
theorem addNuw_refine (x y : iN n)
  : x +nuw y ~> x + y := by blast

@[rule]
theorem addNw_refine (x y : iN n)
  : x +nw y ~> x + y := by blast

@[rule]
theorem add_assoc (x y z : iN n)
    : (x + y) + z <~> x + (y + z) := by blast

-- TODO support disjunction in hypotheses
/- @[rule]
theorem addNsw_assoc_same_sign {hn : Bits64 n} (x y z : iN n)
    (h :
      (x ≥ₛ 0) &&& (y ≥ₛ 0) &&& (z ≥ₛ 0) ~> 1 ∨
      (x <ₛ 0) &&& (y <ₛ 0) &&& (z <ₛ 0) ~> 1)

    : (x +nsw y) +nsw z <~> x +nsw (y +nsw z) := by blast hn -/

/- @[rule]
theorem addNuw_assoc {n} {hn : Bits64 n} (x y z : iN n)
    : (x +nuw y) +nuw z <~> x +nuw (y +nuw z) := by blast hn -/

theorem addNuw_assoc {n} {hn : Bits64 n} (x y z : iN n)
    : (x +nuw y) +nuw z <~> x +nuw (y +nuw z) := by

  iN_convert_goal_bitvec
  simp [simp_iN]
  cases hn
  all_goals bv_decide +acNf

end iN
