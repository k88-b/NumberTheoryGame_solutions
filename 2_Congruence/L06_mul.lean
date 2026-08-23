have step1 := mod_mul_const a b c m h1
have step2 := mod_mul_const c d b m h2
have step2_symm : (b * c) ≡ (b * d) (mod m) := by
  have hrw1 : b * c = c * b := by ring
  have hrw2 : b * d = d * b := by ring
  rw [hrw1, hrw2]
  exact step2
exact mod_trans (a * c) (b * c) (b * d) m step1 step2_symm
