unfold ModEq at *
obtain ⟨k1, hk1⟩ := h1
obtain ⟨k2, hk2⟩ := h2
use k2 * k1
rw [hk1, hk2]
ring
