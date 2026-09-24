have hd1_amk : d1 ∣ a + m * k := h1.1.1
have hd1_m : d1 ∣ m := h1.1.2
have hd2_a : d2 ∣ a := h2.1.1
have hd2_m : d2 ∣ m := h2.1.2

have hd1_a : d1 ∣ a := by
  obtain ⟨x, hx⟩ := hd1_amk
  obtain ⟨y, hy⟩ := hd1_m
  use x - y * k
  have h_eq1 : a = (a + m * k) - m * k := by ring
  rw [h_eq1, hx, hy]
  ring

have hd1_d2 : d1 ∣ d2 := gcd_is_greatest a m d1 d2 h2 hd1_a hd1_m

have hd2_amk : d2 ∣ a + m * k := by
  obtain ⟨x, hx⟩ := hd2_a
  obtain ⟨y, hy⟩ := hd2_m
  use x + y * k
  rw [hx, hy]
  ring

have hd2_d1 : d2 ∣ d1 := gcd_is_greatest (a + m * k) m d2 d1 h1 hd2_amk hd2_m

exact dvd_antisymm hd1 hd2 hd1_d2 hd2_d1
