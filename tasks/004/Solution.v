Require Import Problem.

Theorem solution : task.
Proof.
  unfold task.
  intros.
  remember (f b) as x; remember (f (negb b)) as y.
  destruct b; destruct x; repeat rewrite <- Heqx; auto.
  all: simpl in Heqy; rewrite <- Heqy; destruct y; auto.
Qed.
