have h_exists : ∃ k, (a * k) ≡ 1 (mod m) := by
  use x
have h_coprime : IsGCD(a, m) 1 := inv_implies_coprime a m h_exists
have h_trans : (a * x) ≡ (a * y) (mod m) := by
  have hy_symm := mod_symm (a * y) 1 m hy
  exact mod_trans (a * x) 1 (a * y) m hx hy_symm
have h_eq : (x * a) ≡ (y * a) (mod m) := by
  have hrw1 : x * a = a * x := by ring
  have hrw2 : y * a = a * y := by ring
rw [hrw1, hrw2]
exact h_trans
exact mod_cancel_coprime x y a m h_eq h_coprime
