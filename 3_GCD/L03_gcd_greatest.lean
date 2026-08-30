unfold IsGCD at h

obtain ⟨⟨hda, hdb⟩, x, y, hxy⟩ := h

have h1 : c ∣ (a * x)
· exact dvd_mul_of_dvd_left hca x

have h2 : c ∣ (b * y)
· exact dvd_mul_of_dvd_left hcb y

obtain ⟨k1, hk1⟩ := h1
obtain ⟨k2, hk2⟩ := h2
use k1 + k2
rw [← hxy, hk1, hk2]

ring
