unfold ModEq at hm hn
unfold ModEq
obtain ⟨k1, hk1⟩ := hm
obtain ⟨k2, hk2⟩ := hn
have h_eq : m * k1 = n * k2 := by rw [← hk1, hk2]
have h_div : m ∣ (k2 * n) := by
  use k1
  have h_eq2 : k2 * n = n * k2 := by ring
  rw [h_eq2, ← h_eq]
have h_coprime_symm : IsGCD(n, m) 1 := by
  unfold IsGCD at h_coprime
  unfold IsGCD
  obtain ⟨_, u, v, huv⟩ := h_coprime
  constructor
  · constructor
    · exact one_dvd n
    · exact one_dvd m
  · use v, u
    have h_eq3 : n * v + m * u = m * u + n * v := by ring
    rw [h_eq3, huv]
obtain ⟨k3, hk3⟩ := euclids_lemma k2 n m h_div h_coprime_symm
use k3
rw [hk2, hk3]
ring
