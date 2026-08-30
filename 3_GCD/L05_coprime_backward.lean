unfold IsGCD
constructor
· constructor
  · Hint (hidden := true) "Remember the theorem `one_dvd` from World 1? It proves that 1 divides everything."
    exact one_dvd c
  · exact one_dvd m

· exact h
