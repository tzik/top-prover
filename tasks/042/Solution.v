Require Import Problem.

Theorem solution: task.
Proof.
  unfold task.
  unfold ext_eq.
  intros.
  specialize (H a).
  rewrite H.
  auto.
Qed.
