Require Import Problem.

Theorem solution: task.
Proof.
  unfold task.
  intros.
  remember (P true) as x.
  destruct x.
  - remember (P false) as y.
    destruct y; [exists true|exists false]; destruct x; auto.
  - exists true.
    rewrite <- Heqx.
    discriminate.
Qed.
