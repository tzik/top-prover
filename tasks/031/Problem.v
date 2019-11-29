Require Import Arith.

Fixpoint binom m n :=
  match m, n with
  | _, 0 => 1
  | 0, _ => 0
  | S m', S n' => binom m' n + binom m' n'
  end.

Fixpoint binom_sum n k :=
  match k with 0 => 1 | S k' => binom n k + binom_sum n k' end.

Definition task := forall n, binom_sum n n = 2^n.
