unfold IsGCD at hd
obtain ⟨_, u, v, huv⟩ := hd
obtain ⟨k, hk⟩ := hb
use u * k
unfold ModEq
use -v * k
rw [hk]
have h_eq : a * (u * k) - d * k = m * (-v * k) + k * (a * u + m * v - d) := by ring
rw [h_eq, huv]
ring
