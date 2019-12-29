Require Import Problem Permutation List.
Import ListNotations.

Theorem solution: task.
Proof.
  unfold task.
  intros.
  apply Permutation_length_1.
  apply (Permutation_app_inv_r l).
  auto.
Qed.
