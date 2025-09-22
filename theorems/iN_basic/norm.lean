import theorems.iN.iN
import theorems.Core.Attrs.Attrs

namespace iN

@[rule ideal const (2 3)]
theorem canon (x y con1 con2 : iN n)
    : (x + con1) - (y + con2) <~> (x - y) + (con1 - con2) := by blast

@[rule ideal]
theorem refine (x y : iN n)
    : x +nsw y ~> x + y := by blast

@[rule]
theorem refine1
    : (poison : iN n) ~> 2 := Rewrite.poison_forge 2

@[rule]
theorem refine32
    : (poison : iN 32) ~> 2 := Rewrite.poison_forge 2

theorem hypot0 {hn : Bits64 n}
    : (poison : iN n) ~> 2 := Rewrite.poison_forge 2

@[rule]
theorem better2 {hn : Bits64 n} (x : iN n)
    (h : x ≥ₛ 0 ~> 1)
    : x ~> x := by

  blast

end iN
