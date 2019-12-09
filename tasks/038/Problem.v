Require Export Arith.

Definition task :=
  forall m n, S m < n -> m < (m + n) / 2 < n.
