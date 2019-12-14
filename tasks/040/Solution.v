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
    destruct H3; [auto|].
    rewrite (H (S m) n H3 H2) in H1.
    discriminate.
  - apply (H n m); auto.
Qed.

Theorem solution: task.
Proof.
  unfold task.
  intros f H l r.
  remember (r - l) as k.
  assert (r <= S k + l) by omega; clear Heqk.
  revert l r H0.

  induction k; intros.
  - assert (S l = r) by omega.
    subst r.
    clear H0 H1.
    exists 0.
    simpl.
    rewrite Nat.eqb_refl.
    apply boundary; auto.
  - cut (exists k0 : nat, forall n : nat, f n = true <-> n <= binsearch f l r (S k0)).
    * intro; destruct H4; exists (S x); auto.
    * simpl.
      destruct r; [exfalso; omega|].
      assert (l = r \/ l < r) by omega.
      destruct H4.
      + subst r.
        rewrite Nat.eqb_refl.
        exists 0.
        apply boundary; auto.
      + assert (l <> r) by omega.
        apply Nat.eqb_neq in H5.
        rewrite H5; clear H5.
        fold ((l + S r) / 2).
        assert (l < (l + S r) / 2 < S r) by (apply midpoint; omega).
        remember (((l + S r) / 2)) as m.
        remember (f m).
        destruct b; apply IHk; auto; omega.
Qed.
