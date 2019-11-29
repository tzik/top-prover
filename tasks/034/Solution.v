Require Import Problem List.

Theorem solution : task.
Proof.
  unfold Problem.task.
  intro.
  induction t.
  intros.
  destruct t'; auto.
  specialize (H nil); simpl in H; discriminate.

  intros.
  destruct t'.
  specialize (H nil); simpl in H; discriminate.

  assert (v = v0).
  specialize (H nil); simpl in H; inversion H; auto.
  subst v0.

  assert (t1 = t'1).
  specialize (IHt1 t'1).
  clear IHt2.
  apply IHt1.
  intros.
  specialize (H (false :: i)).
  simpl in H.
  auto.

  subst t'1.
  assert (t2 = t'2).
  specialize (IHt2 t'2).
  clear IHt1.
  apply IHt2.
  intros.
  specialize (H (true :: i)).
  simpl in H.
  auto.

  subst t'2.
  auto.
Qed.
