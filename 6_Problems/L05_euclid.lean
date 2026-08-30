have h_gcd : IsGCD 3 10 1
· unfold IsGCD
  constructor
  · constructor
    · exact one_dvd 3
    · exact one_dvd 10
  · use -3, 1
    ring

exact euclids_lemma x 3 10 h h_gcd
