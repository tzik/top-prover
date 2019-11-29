Require Import Problem PeanoNat Omega.

Theorem solution: task.
Proof.
  unfold task.
  intros.
  destruct (Nat.eq_add_1 m n H); omega.
Qed.
