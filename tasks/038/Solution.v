Require Import Problem Omega.

Theorem solution: task.
Proof.
  unfold task.
  intros.
  split.
  - apply Nat.div_le_lower_bound; omega.
  - apply Nat.div_lt_upper_bound; omega.
Qed.
