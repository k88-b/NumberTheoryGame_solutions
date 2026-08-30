obtain ⟨x, hx⟩ := h
unfold ModEq at hx
obtain ⟨k, hk⟩ := hx

have h_bezout : ∃ u v : ℤ, a * u + m * v = 1
· use x, -k

  have h_eq : a * x + m * (-k) = (a * x - 1) - m * k + 1
  · ring

  rw [h_eq, hk]
  ring

exact bezout_imp_coprime a m h_bezout
