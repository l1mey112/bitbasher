import theorems.iN

/- # x + 0 -/

@[opt ideal]
theorem add_zero {n} (x : iN n) : x + 0 ~> x := by
  cases x
  all_goals simp [simp_iN]

@[opt ideal]
theorem addNsw_zero {n} (x : iN n) : x +nsw 0 ~> x := by
  cases x
  all_goals simp [simp_iN]

@[opt ideal]
theorem addNuw_zero {n} (x : iN n) : x +nuw 0 ~> x := by
  cases x
  all_goals simp [simp_iN]

@[opt ideal]
theorem addNw_zero {n} (x : iN n) : x +nw 0 ~> x := by
  cases x
  all_goals simp [simp_iN]

/- # x - 0 -/

@[opt ideal]
theorem sub_zero {n} (x : iN n) : x - 0 ~> x := by
  cases x
  all_goals simp [simp_iN]

@[opt ideal]
theorem subNsw_zero {n} (x : iN n) : x -nsw 0 ~> x := by
  cases x
  all_goals simp [simp_iN]

@[opt ideal]
theorem subNuw_zero {n} (x : iN n) : x -nuw 0 ~> x := by
  cases x
  all_goals simp [simp_iN]

@[opt ideal]
theorem subNw_zero {n} (x : iN n) : x -nw 0 ~> x := by
  cases x
  all_goals simp [simp_iN]
