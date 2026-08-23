have h10 := div10_rule k d
have h2 : (2 : ℤ) ∣ 10 := by
  use 5
  ring
exact mod_shrink (10 * k + d) d 10 2 h10 h2
