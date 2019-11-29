Fixpoint double n :=
  match n with
  | 0 => 0
  | 1 => 2
  | S (S n') => S (S (S (S (double n'))))
  end.

Definition task := forall n, double n = 2 * n.
