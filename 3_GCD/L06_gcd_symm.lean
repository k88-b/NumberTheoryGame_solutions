unfold IsGCD at *
obtain ⟨⟨hda, hdb⟩, x, y, hxy⟩ := h
constructor
· constructor
  · exact hdb
  · exact hda
use y, x

have h_eq : b * y + a * x = a * x + b * y
· ring

rw [h_eq, hxy]
