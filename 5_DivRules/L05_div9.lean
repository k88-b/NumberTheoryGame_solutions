have h10 : 10 ≡ 1 (mod 9) := by
  unfold ModEq
  use 1
  ring
exact polynomial_cong 10 1 c0 c1 c2 9 h10
