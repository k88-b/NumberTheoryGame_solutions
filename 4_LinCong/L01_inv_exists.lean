unfold IsGCD at h
obtain ⟨_, x, y, hxy⟩ := h
use x
unfold ModEq
use -y

have h_eq : a * x - 1 = (a * x + m * y) - 1 - m * y
· ring

rw [h_eq, hxy]
· ring
