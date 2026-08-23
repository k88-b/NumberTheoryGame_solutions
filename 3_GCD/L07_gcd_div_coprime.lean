unfold IsGCD at *
obtain ⟨_, x, y, hxy⟩ := h
constructor
· constructor
  · exact one_dvd c1
  · exact one_dvd m1
· use x, y
  have e : d * (c1 * x + m1 * y) = c1 * d * x + m1 * d * y := by ring
  have h_eq : d * (c1 * x + m1 * y) = d * 1 := by
    rw [e, ← hc, ← hm, hxy]
    ring
  exact mul_left_cancel₀ hd h_eq
