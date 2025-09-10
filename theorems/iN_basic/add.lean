import theorems.iN.iN

namespace iN

-- TODO mark not `@[rewrite]` but something for directional equality

@[grind]
theorem add_comm {n} (x y : iN n)
    : x + y = y + x := by

  -- clear poison from `x` and `y`
  simp only [iN_unwrap_poison]
  repeat' split; <;> try simp [*] at *

  grind

@[grind]
theorem addNsw_comm {n} (x y : iN n)
    : x +nsw y <~> y +nsw x := by

  -- clear poison from `x` and `y`
  simp only [iN_unwrap_poison]

  cases x
  . cases y
    . simp [*] at *
      grind
    . simp
  . simp
    -- TODO https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Simp.20not.20collapsing.20simultaneous.20matching/with/538586043
    grind

@[grind]
theorem addNuw_comm {n} (x y : iN n)
    : x +nuw y <~> y +nuw x := by

  -- clear poison from `x` and `y`
  simp only [iN_unwrap_poison]

  cases x
  . cases y
    . simp [*] at *
      grind
    . simp
  . simp
    -- TODO https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/Simp.20not.20collapsing.20simultaneous.20matching/with/538586043
    grind

@[grind]
theorem add_assoc {n} (x y z : iN n)
    : (x + y) + z = x + (y + z) := by

  -- clear poison from `x` and `y`
  simp only [iN_unwrap_poison]

  cases x
  . cases y
    . cases z
      . simp
        grind
      . simp
    . simp
  . simp

/- @[grind]
theorem addNsw_assoc {n} (x y z : iN n)
    : (x +nsw y) +nsw z <~> x +nsw (y +nsw z) := by

  -- clear poison from `x` and `y`
  simp only [iN_unwrap_poison]

  cases x
  . cases y
    . cases z
      . simp



      . simp
    . simp
  . simp -/

end iN
