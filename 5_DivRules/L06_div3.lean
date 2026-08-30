have h9 : (c2 * 10 ^ 2 + c1 * 10 + c0) ≡ c2 * 1 ^ 2 + c1 * 1 + c0 (mod 9)
· exact div9_rule_3 c0 c1 c2

have h3 : (3 : ℤ) ∣ 9
· use 3
  ring

exact mod_shrink (c2 * 10^2 + c1 * 10 + c0) (c2 * 1^2 + c1 * 1 + c0) 9 3 h9 h3
