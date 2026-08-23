have h_gcd : IsGCD 14 9 1 := by
  unfold IsGCD
  constructor
  · constructor
    · exact one_dvd 14
    · exact one_dvd 9
  · use 2, -3
    ring

have h_swap : (x * 14) ≡ (y * 14) (mod 9) := by
  have hrw1 : x * 14 = 14 * x := by ring
  have hrw2 : y * 14 = 14 * y := by ring
  rw [hrw1, hrw2]
  exact h

exact mod_cancel_coprime x y 14 9 h_swap h_gcd
