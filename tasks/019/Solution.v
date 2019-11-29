Require Import Problem PeanoNat Omega.

Lemma lemma : forall n l, list_in l n = false -> List.count_occ Nat.eq_dec l n = 0.
Proof.
  intros.
  induction l.
  simpl; auto.

  simpl; simpl in H.
  destruct (Nat.eq_dec a n).
  subst a.
  specialize (Nat.eqb_eq n n); intro.
  destruct H0; clear H0.
  rewrite (H1 eq_refl) in H.
  discriminate.

  destruct (Nat.eqb n a).
  discriminate.

  auto.
Qed.

Lemma lemma2 : forall l n, list_in l n = false -> list_in (unique l) n = false.
Proof.
  intros.
  induction l.
  simpl; auto.

  simpl in H; simpl.
  remember (Nat.eqb n a).
  destruct b.
  discriminate.

  destruct (list_in l a).
  auto.

  simpl.
  rewrite <- Heqb.
  auto.
Qed.

Theorem solution : task.
Proof.
  unfold Problem.task.
  intros.
  induction l.
  discriminate.

  simpl in H; simpl.

  specialize (Nat.eqb_eq n a); intro.
  destruct H0; clear H1.
  remember (Nat.eqb n a) as b.
  destruct b.
  clear Heqb.
  specialize (H0 H); clear H.
  subst a.

  remember (list_in l n).
  destruct b.
  exact (IHl eq_refl).
  clear IHl.

  simpl.
  destruct (Nat.eq_dec n n).
  clear e.

  simpl.
  rewrite lemma.
  auto.
  apply lemma2.
  auto.
  contradiction.

  clear H0.
  remember (list_in l a).
  destruct b.
  apply IHl; auto.

  simpl.
  destruct (Nat.eq_dec a n).
  subst a.
  rewrite Nat.eqb_refl in Heqb.
  discriminate.
  auto.
Qed.
