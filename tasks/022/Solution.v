Require Import Problem.

Theorem solution: task1 \/ task2.
Proof.
  right.
  unfold task2.
  split; intros.
  - contradict H.
    destruct H; contradict H; destruct H; auto.
  - split; contradict H; auto.
Qed.
