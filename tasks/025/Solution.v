Require Import Problem.

Theorem solution : task.
Proof.
  unfold task.
  destruct a; destruct b; auto; destruct c; auto.
Qed.
