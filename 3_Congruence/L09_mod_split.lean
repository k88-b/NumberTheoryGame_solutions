constructor
· unfold ModEq at *
  obtain ⟨k, hk⟩ := h
  use n * k
  rw [hk]
  ring
· unfold ModEq at *
  obtain ⟨k, hk⟩ := h
  use m * k
  rw [hk]
  ring
