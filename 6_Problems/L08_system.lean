unfold ModEq at *
obtain ⟨k1, hk1⟩:= h1
obtain ⟨k2,hk2⟩ := h2

have h4: 11 ∣ (x * 25)
· use 3 * k1 + 4 * k2

  have h: 11 * (3 * k1 + 4 * k2) = (11 * k1) * 3 + (11 * k2) * 4
  · ring

  rw [h, ← hk1, ← hk2]
  ring

have h_coprime : IsGCD 25 11 1
· unfold IsGCD
  constructor
  · constructor
    · exact one_dvd 25
    · exact one_dvd 11

  · use 4, -9
    ring

have h: x - 0 = x
· ring

rw [h]

exact euclids_lemma x 25 11  h4 h_coprime
