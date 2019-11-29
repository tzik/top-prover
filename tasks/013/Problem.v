Definition injective1 (f : nat -> nat) : Prop :=
  forall m n, f m = f n -> m = n.

Definition injective2 (f : nat -> nat) : Prop :=
  forall m n, m <> n -> f m <> f n.

Definition task := forall f, injective1 f <-> injective2 f.
