Require Import Problem.

Theorem solution : task.
Proof.
  unfold Problem.task.
  split; intros.
  apply (R_trans x y z); auto.
  exact (H y (R_refl y)).
Qed.
