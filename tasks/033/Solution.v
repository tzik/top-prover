Require Import Problem.

Theorem solution : task.
Proof.
  unfold Problem.task.
  intros.
  inversion H.
  auto.
Qed.
