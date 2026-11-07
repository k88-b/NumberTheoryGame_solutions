unfold ModEq at hm hn
unfold ModEq
obtain ⟨k1, hk1⟩ := hm
obtain ⟨k2, hk2⟩ := hn

have h_eq : m * k1 = n * k2
· rw [← hk1, hk2]

have h_div : m ∣ (k2 * n)
· use k1

  have h_eq2 : k2 * n = n * k2
  · ring

  rw [h_eq2, ← h_eq]

have h_coprime_symm : IsGCD n m 1
· exact gcd_symm m n 1 h_coprime

obtain ⟨k3, hk3⟩ := euclids_lemma k2 n m h_div h_coprime_symm

use k3
rw [hk2, hk3]

ring
