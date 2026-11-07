unfold IsGCD at h
obtain ⟨⟨hda, hdb⟩, x, y, hxy⟩ := h
rw [← hxy]
exact dvd_lin_comb_int c a b x y hca hcb
