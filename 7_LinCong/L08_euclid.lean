have h_cong : (a * c) ≡ (0 * c) (mod m)
· unfold ModEq

  have h_eq1 : a * c - 0 * c = a * c
  · ring

  rw [h_eq1]
  exact h_div

have h_cancel : a ≡ 0 (mod m)
· exact mod_cancel_coprime a 0 c m h_cong h_coprime

unfold ModEq at h_cancel

have h_eq2 : a = a - 0
· ring

rw [h_eq2]
exact h_cancel
