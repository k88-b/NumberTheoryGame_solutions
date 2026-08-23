have h_pow2 : (a^2) ≡ (b^2) (mod m) := mod_pow a b m 2 h
have h_term2_swap : (a^2 * c2) ≡ (b^2 * c2) (mod m) := mod_mul_const (a^2) (b^2) c2 m h_pow2
have h_term2 : (c2 * a^2) ≡ (c2 * b^2) (mod m) := by
  have hrw1 : c2 * a^2 = a^2 * c2 := by ring
  have hrw2 : c2 * b^2 = b^2 * c2 := by ring
  rw [hrw1, hrw2]
  exact h_term2_swap

have h_term1_swap : (a * c1) ≡ (b * c1) (mod m) := mod_mul_const a b c1 m h
have h_term1 : (c1 * a) ≡ (c1 * b) (mod m) := by
  have hrw1 : c1 * a = a * c1 := by ring
  have hrw2 : c1 * b = b * c1 := by ring
  rw [hrw1, hrw2]
  exact h_term1_swap

have h_term0 : c0 ≡ c0 (mod m) := mod_refl c0 m

have h_sum12 := mod_add (c2 * a^2) (c2 * b^2) (c1 * a) (c1 * b) m h_term2 h_term1
exact mod_add (c2 * a^2 + c1 * a) (c2 * b^2 + c1 * b) c0 c0 m h_sum12 h_term0
