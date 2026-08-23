have h_gcd : IsGCD 5 7 1 := by
  unfold IsGCD
  constructor
  · constructor
    · exact one_dvd 5
    · exact one_dvd 7
  · use 3, -2
    ring

have h_div : (1: ℤ) ∣ 3 := by
  use 3
  ring

exact lin_cong_suff 5 3 7 1 h_gcd h_div
