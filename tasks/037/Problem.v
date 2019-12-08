Inductive iszero : nat -> Prop :=
| iszero_0 : iszero 0
| iszero_S : forall n, iszero (S n) -> iszero n.

Definition task := forall n, iszero n <-> n = 0.
