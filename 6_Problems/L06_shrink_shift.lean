have h_div : (4 : ℤ) ∣ 100 := by
  use 25
  ring

have h_shrink := mod_shrink x 23 100 4 h h_div

have h_23 : 23 ≡ 3 (mod 4) := by
  unfold ModEq
  use 5
  ring

exact mod_trans x 23 3 4 h_shrink h_23
