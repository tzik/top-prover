Require Import Problem PeanoNat.

Theorem solution: task.
Proof.
  unfold task.
  unfold injective1.
  unfold injective2.
  split; intros; [auto|].
  destruct (Nat.eq_dec m n); [auto|].
  apply H in n0.
  contradiction.
Qed.
