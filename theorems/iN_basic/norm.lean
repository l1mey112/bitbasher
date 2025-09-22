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

end iN
