unfold ModEq at *
obtain ⟨k, hk⟩ := h
use k
have h_eq : a * c - b * c = (a - b) * c := by ring
rw [h_eq]
rw [hk]
ring
