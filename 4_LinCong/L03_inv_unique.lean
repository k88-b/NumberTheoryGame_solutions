have h_exists : ∃ k, (a * k) ≡ 1 (mod m)
· use x

have h_coprime : IsGCD a m 1
· exact inv_implies_coprime a m h_exists

have h_trans : (a * x) ≡ (a * y) (mod m)
· have hy_symm : 1 ≡ (a * y) (mod m)
  · exact mod_symm (a * y) 1 m hy

  exact mod_trans (a * x) 1 (a * y) m hx hy_symm

have h_eq : (x * a) ≡ (y * a) (mod m)
· have hrw1 : x * a = a * x
  · ring

  have hrw2 : y * a = a * y
  · ring

  rw [hrw1, hrw2]
  exact h_trans

exact mod_cancel_coprime x y a m h_eq h_coprime
