Require Import Problem.
Require Import Classical.

Theorem solution : task.
Proof.
  unfold task.
  intros.
  destruct (classic P); [auto|exfalso].
  assert (P -> Q) by contradiction.
  auto.
Qed.
