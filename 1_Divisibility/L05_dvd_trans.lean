obtain ⟨k1, hk1⟩ := h1
obtain ⟨k2, hk2⟩ := h2

use k1 * k2

rw [hk2, hk1]
ring
