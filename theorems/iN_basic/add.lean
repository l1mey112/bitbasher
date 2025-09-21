import theorems.iN.iN

namespace iN

theorem add_comm (x y : iN n)
    : x + y <~> y + x := by blast

theorem addNsw_comm (x y : iN n)
    : x +nsw y <~> y +nsw x := by blast

theorem addNuw_comm (x y : iN n)
    : x +nuw y <~> y +nuw x := by blast

theorem addNw_comm (x y : iN n)
    : x +nw y <~> y +nw x := by blast

theorem addNsw_refine (x y : iN n)
  : x +nsw y ~> x + y := by blast

theorem addNuw_refine (x y : iN n)
  : x +nuw y ~> x + y := by blast

theorem addNw_refine (x y : iN n)
  : x +nw y ~> x + y := by blast

theorem add_assoc (x y z : iN n)
    : (x + y) + z <~> x + (y + z) := by blast

theorem addNsw_assoc_same_sign {hn : Bits n} (x y z : iN n)
    (h :
      (x ≥ₛ 0) &&& (y ≥ₛ 0) &&& (z ≥ₛ 0) ~> 1 ∨
      (x <ₛ 0) &&& (y <ₛ 0) &&& (z <ₛ 0) ~> 1)

    : (x +nsw y) +nsw z <~> x +nsw (y +nsw z) := by blast hn

theorem addNuw_assoc {n} {hn : Bits n} (x y z : iN n)
    : (x +nuw y) +nuw z <~> x +nuw (y +nuw z) := by blast hn

end iN
