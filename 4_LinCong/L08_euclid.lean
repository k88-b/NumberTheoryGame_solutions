have h_cong_direct : (a * c) ≡ (0 * c) (mod m) := by
  unfold ModEq
  obtain ⟨k, hk⟩ := h_div
  use k
  have h_eq : a * c - 0 * c = a * c := by ring
  rw [h_eq]
  exact hk
have h_cancel := mod_cancel_coprime a 0 c m h_cong_direct h_coprime
unfold ModEq at h_cancel
obtain ⟨k2, hk2⟩ := h_cancel
use k2
have h_eq2 : a = a - 0 := by ring
rw [h_eq2, hk2]
