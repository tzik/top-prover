Require Import Problem.

Theorem solution: task.
Proof.
  unfold task.
  unfold ext_eq.
  intros.
  rewrite H.
  auto.
Qed.
