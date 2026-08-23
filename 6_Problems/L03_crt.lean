have h_gcd : IsGCD 10 3 1 := by
  unfold IsGCD
  constructor
  · constructor
    · exact one_dvd 10
    · exact one_dvd 3
  · use 1, -3
    ring

exact crt_exists 7 2 10 3 h_gcd
