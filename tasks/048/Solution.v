Require Import Problem Omega.

Theorem solution: task.
Proof.
  unfold task.
  intros.
  destruct H; omega.
Qed.
