have h1 : 17 ≡ 2 (mod 5)
· unfold ModEq
  use 3
  ring

have h2 : 12 ≡ 2 (mod 5)
· unfold ModEq
  use 2
  ring

have h3 : (17 ^ 100) ≡ (2 ^ 100) (mod 5)
· exact mod_pow 17 2 5 100 h1

have h4 : (12 ^ 100) ≡ (2 ^ 100) (mod 5)
· exact mod_pow 12 2 5 100 h2

exact mod_add (17^100) (2^100) (12^100) (2^100) 5 h3 h4
