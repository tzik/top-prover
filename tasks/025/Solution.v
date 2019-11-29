Require Import Problem.

Theorem solution : task.
Proof.
  unfold Problem.task.
  destruct a; destruct b; auto; destruct c; auto.
Qed.
