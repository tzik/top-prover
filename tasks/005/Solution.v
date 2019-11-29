Require Import Problem PeanoNat.

Theorem solution : task.
Proof.
  unfold Problem.task.
  intros.
  rewrite Nat.mul_comm.
  simpl.
  rewrite Nat.mul_comm.
  auto.
Qed.
