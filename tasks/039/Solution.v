Require Import Problem.

Theorem solution: task.
Proof.
  unfold task.
  intros.
  specialize (H True False P).
  repeat destruct H; auto.
Qed.
