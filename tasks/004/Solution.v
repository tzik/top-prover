Require Import Problem.

Theorem solution : task.
Proof.
  unfold task.
  intros.
  remember (f true) as x; remember (f false) as y.
  destruct b; destruct x; destruct y.
  all: repeat (try rewrite <- Heqx; try rewrite <- Heqy); auto.
Qed.
