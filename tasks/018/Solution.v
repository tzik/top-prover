Require Import Problem.

Lemma lemma : forall l a, list_in l a = false -> list_in (unique l) a = false.
Proof.
  intros.
  induction l.
  simpl; auto.

  simpl in H; simpl.
  remember (Nat.eqb a a0).
  destruct b.
  discriminate.
  destruct (list_in l a0).
  auto.
  simpl.
  rewrite <- Heqb.
  auto.
Qed.

Theorem solution : task.
Proof.
  unfold Problem.task.
  induction l.
  simpl; auto.

  simpl.
  remember (list_in l a).
  destruct b.
  auto.
  simpl.
  rewrite IHl.
  rewrite lemma.
  auto.
  auto.
Qed.
