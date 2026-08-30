unfold ModEq at *
obtain ⟨k, hk⟩ := h
use k * c

have h_eq : a * c - b * c = (a - b) * c
· ring

rw [h_eq, hk]
ring
