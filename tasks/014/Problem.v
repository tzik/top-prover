Fixpoint mod2 n :=
  match n with
  | 0 => 0
  | S n' => match mod2 n' with 0 => 1 | S _ => 0 end
  end.

Definition task := forall n, mod2 n = mod2 (n * n).
