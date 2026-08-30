have hcoprime : IsGCD c1 m1 1
· exact gcd_div_coprime c m d c1 m1 hd h2 hc hm
unfold ModEq at h1
obtain ⟨k, hk⟩ := h1
rw [hc, hm] at hk

have e : a * (c1 * d) - b * (c1 * d) = d * (a * c1 - b * c1)
· ring

have e2 : m1 * d * k = d * (m1 * k)
· ring

rw [e, e2] at hk

have hk2 : a * c1 - b * c1 = m1 * k
· exact mul_left_cancel₀ hd hk

have h1' : (a * c1) ≡ (b * c1) (mod m1)
· unfold ModEq
  use k

exact mod_cancel_coprime a b c1 m1 h1' hcoprime
