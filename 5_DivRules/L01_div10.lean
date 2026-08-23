have h_eq : 10 * k + d = d + k * 10 := by ring
rw [h_eq]
exact mod_add_multiple d k 10
