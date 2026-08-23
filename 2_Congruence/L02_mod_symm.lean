unfold ModEq at *
obtain ⟨k, hk⟩ := h
use -k
have h_eq : b - a = -(a - b) := by ring
rw [h_eq, hk]
ring
