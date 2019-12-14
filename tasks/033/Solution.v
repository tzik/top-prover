Require Import Problem.

Theorem solution : task.
Proof.
  unfold task.
  intros.
  inversion H.
  auto.
Qed.
