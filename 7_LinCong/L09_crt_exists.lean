unfold IsGCD at h_coprime
obtain ⟨_, u, v, huv⟩ := h_coprime

use a * n * v + b * m * u

constructor
· unfold ModEq

  use b * u - a * u

  have h_eq : (a * n * v + b * m * u) - a = m * (b * u - a * u) + a * (m * u + n * v - 1)
  · ring

  rw [h_eq, huv]
  ring

· unfold ModEq

  use a * v - b * v

  have h_eq : (a * n * v + b * m * u) - b = n * (a * v - b * v) + b * (m * u + n * v - 1)
  · ring

  rw [h_eq, huv]

  ring
