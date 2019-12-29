Require Import Problem.

Theorem solution : task.
Proof.
  unfold task.
  split; intros.
  - apply (R_trans x y z); auto.
  - apply H; apply R_refl.
Qed.
