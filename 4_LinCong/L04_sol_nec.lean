unfold IsGCD at hd
obtain ⟨⟨hda, hdm⟩, _⟩ := hd

unfold ModEq at hx
obtain ⟨k, hk⟩ := hx

have h1 : d ∣ (a * x)
· exact dvd_mul_of_dvd_left hda x

have h2 : d ∣ (m * k)
· exact dvd_mul_of_dvd_left hdm k

obtain ⟨k1, hk1⟩ := h1
obtain ⟨k2, hk2⟩ := h2

use k1 - k2

have h_eq : b = a * x - m * k
· rw [← hk]
  ring

rw [h_eq, hk1, hk2]
ring
