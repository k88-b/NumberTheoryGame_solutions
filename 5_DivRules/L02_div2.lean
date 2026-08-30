have h10 : (10 * k + d) ≡ d (mod 10)
· exact div10_rule k d

have h2 : (2 : ℤ) ∣ 10
· use 5
  ring

exact mod_shrink (10 * k + d) d 10 2 h10 h2
