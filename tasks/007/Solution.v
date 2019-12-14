Require Import Problem PeanoNat Omega.

Definition f m n := product_of_range m n.

Lemma extract_l (m n : nat) : f m (S n) = S m * f (S m) n.
Proof.
  simpl.
  auto.
Qed.

Lemma extract_r (m n : nat) : f m (S n) = (m + S n) * f m n.
Proof.
  revert m.
  induction n; intros; [simpl; omega|].
  rewrite extract_l.
  rewrite IHn; clear IHn.
  rewrite extract_l.
  remember (f (S m) n) as k eqn:H; clear H.
  remember (S n) as n' eqn:H; clear H n.
  rewrite Nat.add_succ_comm.
  remember (m + S n') as a eqn:H; clear H n'.
  repeat rewrite Nat.mul_assoc.
  rewrite (Nat.mul_comm (S m) a).
  omega.
Qed.

Lemma extract_r_0 (n : nat) : f 0 (S n) = S n * f 0 n.
Proof.
  intros.
  rewrite extract_r.
  auto.
Qed.

Lemma lemma (o m n : nat) : m + n = o -> exists k, f m n = k * f 0 n.
Proof.
  revert m n.
  induction o; intros.
  - apply Nat.eq_add_0 in H; destruct H.
    subst m n; exists 1; auto.
  - destruct m; simpl; destruct n.
    + discriminate.
    + exists 1; omega.
    + exists 1; simpl; omega.
    + assert (m + S n = o) by omega.
      assert (S m + n = o) by omega.
      clear H.
      destruct (IHo m (S n) H0) as [x]; clear H0.
      destruct (IHo (S m) n H1) as [y]; clear H1.
      clear IHo o.
      rewrite extract_r.
      rewrite Nat.mul_add_distr_r.
      rewrite <- extract_l.
      rewrite H; clear H.
      rewrite H0; clear H0.
      rewrite Nat.mul_assoc.
      rewrite (Nat.mul_comm (S n) y).
      rewrite <- Nat.mul_assoc.
      replace (S n * f 0 n) with (f 0 (S n)) by (rewrite extract_r; auto).
      exists (x + y).
      remember (f 0 (S n)) as a; clear Heqa m n.
      rewrite Nat.mul_add_distr_r; auto.
Qed.

Theorem solution : task.
Proof.
  unfold task.
  intros m n.
  destruct (lemma (m + n) m n eq_refl) as [k].
  exists k.
  unfold f in H.
  omega.
Qed.
