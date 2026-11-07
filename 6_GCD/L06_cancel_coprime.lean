unfold ModEq at *
unfold IsGCD at h2
obtain ⟨k, hk⟩ := h1
obtain ⟨_, x, y, hxy⟩ := h2

use k * x + (a - b) * y

have h_eq1 : m * (k * x + (a - b) * y) = (m * k) * x + (a - b) * (m * y)
· ring

have h_eq2 : (a * c - b * c) * x + (a - b) * (m * y) = (a - b) * (c * x + m * y)
· ring

rw [h_eq1, ← hk, h_eq2, hxy]

ring
