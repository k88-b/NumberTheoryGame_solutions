unfold ModEq at *
obtain ⟨k1, hk1⟩ := h1
obtain ⟨k2, hk2⟩ := h2

have h : x^2 - 5*x + 6 = (x - 2) * (x - 3)
· ring

rw [h, hk1, hk2]
use k1 * k2
ring

