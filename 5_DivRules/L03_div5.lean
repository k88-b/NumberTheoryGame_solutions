have h10 : (10 * k + d) ≡ d (mod 10)
· exact div10_rule k d

have h5 : (5 : ℤ) ∣ 10
· use 2
  ring

exact mod_shrink (10 * k + d) d 10 5 h10 h5
