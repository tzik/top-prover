Require Import Problem PeanoNat.

Theorem solution: task.
Proof.
  unfold task.
  unfold injective1.
  unfold injective2.
  split; intros.
  - contradict H0.
    auto.
  - destruct (Nat.eq_dec m n).
    * auto.
    * specialize (H m n n0 H0).
      contradiction.
Qed.
