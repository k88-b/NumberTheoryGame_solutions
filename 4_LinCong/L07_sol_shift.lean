unfold IsGCD at hd
obtain ⟨⟨hda, _⟩, _⟩ := hd
obtain ⟨a1, ha1⟩ := hda
have h_shift : (a * (x0 + t * m1)) = a * x0 + (a1 * t) * m := by
  rw [ha1, hm]
  ring
have h_cong : (a * (x0 + t * m1)) ≡ (a * x0) (mod m) := by
  rw [h_shift]
  exact mod_add_multiple (a * x0) (a1 * t) m
exact mod_trans (a * (x0 + t * m1)) (a * x0) b m h_cong h0
