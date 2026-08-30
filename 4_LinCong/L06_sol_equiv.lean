have h_trans : (a * x1) ≡ (a * x2) (mod m)
· have h2_symm : b ≡ (a * x2) (mod m)
  · exact mod_symm (a * x2) b m h2

  exact mod_trans (a * x1) b (a * x2) m h1 h2_symm

have h_eq : (x1 * a) ≡ (x2 * a) (mod m)
· have hrw1 : x1 * a = a * x1
  · ring

  have hrw2 : x2 * a = a * x2
  · ring

  rw [hrw1, hrw2]
  exact h_trans

exact mod_cancel_general x1 x2 a m d a1 m1 hd_not_zero h_eq hd ha hm
