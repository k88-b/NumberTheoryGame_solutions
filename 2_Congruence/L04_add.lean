unfold ModEq at *
obtain ⟨k1, hk1⟩ := h1
obtain ⟨k2, hk2⟩ := h2
use k1 + k2

have h_eq : (a + c) - (b + d) = (a - b) + (c - d)
· ring

rw [h_eq, hk1, hk2]
ring
