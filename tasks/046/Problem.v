Definition swap (t : nat * nat) :=
  match t with (a, b) => (b, a) end.

Definition task := forall t, swap (swap t) = t.
