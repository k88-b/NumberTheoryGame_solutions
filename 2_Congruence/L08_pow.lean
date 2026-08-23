induction' n with d ih
unfold ModEq
use 0
ring
rw [pow_succ, pow_succ]
exact mod_mul (a^d) (b^d) a b m ih h
