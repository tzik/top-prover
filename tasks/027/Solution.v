Require Import Problem.

Definition ge_three (X : Set) := exists a b c : X, a <> b /\ b <> c /\ c <> a.

Theorem solution : task.
Proof.
  unfold task.
  assert (ge_three Three).
  unfold ge_three.
  exists C31; exists C32; exists C33.
  repeat split; discriminate.

  intro.
  rewrite <- H0 in H; clear H0.
  unfold ge_three in H.
  do 3 destruct H.
  destruct H; destruct H0.
  destruct x; destruct x0; destruct x1; auto.
Qed.
