Require Import Problem Omega.

Lemma midpoint (m n : nat) : S m < n -> m < (m + n) / 2 < n.
Proof.
  intros.
  split.
  - apply Nat.div_le_lower_bound; omega.
  - apply Nat.div_lt_upper_bound; omega.
Qed.

Lemma boundary (f : nat -> bool) : downward_closed f -> forall m, f m = true -> f (S m) = false -> forall n, f n = true <-> n <= m.
Proof.
  unfold downward_closed.
  intros.
  split; intro.
  - assert (n <= m \/ S m <= n) by omega.
    destruct H3.
    auto.
    rewrite (H (S m) n H3 H2) in H1.
    discriminate.
  - apply (H n m H2 H0).
Qed.

Theorem solution: task.
Proof.
  unfold task.
  intros f H l r.
  remember (r - l) as k.
  assert (r <= k + l) by omega; clear Heqk.
  revert l r H0.
  induction k; intros.
  omega.

  assert (S l = r \/ S l < r) by omega.
  destruct H4.
  - exists 1.
    subst r.
    simpl.
    rewrite Nat.eqb_refl.
    apply boundary; auto.
  - specialize (midpoint l r H4); intro.
    clear H4 H1.
    remember ((l + r) / 2) as m.
    remember (f m) as b.
    assert (f m = b) by auto; clear Heqb.
    destruct b.
    * assert (r <= k + m) by omega.
      specialize (IHk m r H4 (proj2 H5) H1 H3).
      destruct IHk.
      exists (S x).
      simpl.
      fold ((l + r) / 2); rewrite <- Heqm.
      destruct r.
      exfalso; omega.
      assert (l <> r) by omega.
      apply Nat.eqb_neq in H7.
      rewrite H7.
      rewrite H1.
      auto.
    * assert (m <= k + l) by omega.
      specialize (IHk l m H4 (proj1 H5) H2 H1).
      destruct IHk.
      exists (S x).
      simpl.
      fold ((l + r) / 2); rewrite <- Heqm.
      destruct r.
      exfalso; omega.
      assert (l <> r) by omega.
      apply Nat.eqb_neq in H7.
      rewrite H7.
      rewrite H1.
      auto.
Qed.
