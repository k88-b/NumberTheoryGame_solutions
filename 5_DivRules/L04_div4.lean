have h_eq : 100 * k + d = d + (25 * k) * 4
· ring

rw [h_eq]

exact mod_add_multiple d (25 * k) 4
