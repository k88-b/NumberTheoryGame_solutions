unfold IsGCD
constructor
· Hint "The first goal is *also* an `∧`. Use `constructor` again!"
  constructor
  · use 2
    ring
  · use 3
    ring
· Hint (hidden := true) "To show `2 * x + 3 * y = 1`, try `x = -1` and `y = 1`. Type `use -1, 1`. (use can take multiple witnesses separated by commas)"
  use -1, 1

  ring
