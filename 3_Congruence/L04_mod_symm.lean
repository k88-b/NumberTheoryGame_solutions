unfold ModEq at *
obtain ⟨k, hk⟩ := h
use -k

have h_eq : b - a = -(a - b)
· ring

rw [h_eq, hk]
ring
