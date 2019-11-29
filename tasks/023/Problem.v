Require Import ZArith Znumtheory.

Inductive bin : nat -> Prop :=
  | bin_epsilon : bin 0
  | bin_0 : forall n, bin n -> bin (2 * n)
  | bin_1 : forall n, bin n -> bin (2 * n + 1)
  .
Definition is_expressible_in_binary_notation := bin.

Definition task := forall n, is_expressible_in_binary_notation n.
