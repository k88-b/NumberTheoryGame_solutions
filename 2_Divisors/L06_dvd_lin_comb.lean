obtain ⟨k1, hk1⟩ := ha
obtain ⟨k2, hk2⟩ := hb
rw [hk1, hk2]
use k1 * x + k2 * y
ring
