import theorems.iN.iN

namespace iN

theorem add_comm {hn : Bits n} (x y : iN n)
    : x + y <~> y + x := by blast hn

theorem addNsw_comm {hn : Bits n} (x y : iN n)
    : x +nsw y <~> y +nsw x := by blast hn

theorem addNuw_comm {hn : Bits n} (x y : iN n)
    : x +nuw y <~> y +nuw x := by blast hn

theorem addNw_comm {hn : Bits n} (x y : iN n)
    : x +nw y <~> y +nw x := by blast hn

theorem addNsw_refine (x y : iN n)
  : x +nsw y ~> x + y := by blast hn

theorem addNuw_refine (x y : iN n)
  : x +nuw y ~> x + y := by blast hn

theorem addNw_refine (x y : iN n)
  : x +nw y ~> x + y := by blast hn

theorem add_assoc {hn : Bits n} (x y z : iN n)
    : (x + y) + z <~> x + (y + z) := by blast hn

@[grind]
theorem addNsw_assoc_same_sign {hn : Bits n} (x y z : iN n)
    (h :
      (x ≥ₛ 0) &&& (y ≥ₛ 0) &&& (z ≥ₛ 0) ~> 1 ∨
      (x <ₛ 0) &&& (y <ₛ 0) &&& (z <ₛ 0) ~> 1)

    : (x +nsw y) +nsw z <~> x +nsw (y +nsw z) := by blast hn

@[grind]
theorem addNuw_assoc {n} {hn : Bits n} (x y z : iN n)
    : (x +nuw y) +nuw z <~> x +nuw (y +nuw z) := by blast hn

end iN
