Require Import Problem PeanoNat Omega.

Lemma binom_n_Sn (n : nat) : binom n (S n) = 0.
Proof.
  remember (S n) as k.
  assert (k > n) by omega; clear Heqk.
  generalize k H; clear k H.
  induction n; simpl; intros.
  - destruct k; omega.
  - destruct k.
    * omega.
    * assert (k > n) by omega; clear H.
      rewrite (IHn k H0).
      assert (S k > n) by omega; clear H0.
      rewrite (IHn (S k) H).
      auto.
Qed.

Lemma binom_sum_split (m n : nat) : binom_sum (S m) (S n) = binom_sum m (S n) + binom_sum m n.
Proof.
  simpl.
  repeat rewrite <- Nat.add_assoc.
  apply Nat.add_cancel_l.
  induction n.
  * destruct m; simpl; auto.
  * simpl.
    repeat rewrite <- Nat.add_assoc.
    rewrite IHn.
    omega.
Qed.

Theorem solution: task.
Proof.
  unfold task.
  induction n.
  - auto.
  - replace (2 ^ S n) with (2 * 2^n) by (simpl; omega).
    rewrite <- IHn; clear IHn.
    rewrite binom_sum_split.
    simpl.
    rewrite binom_n_Sn.
    auto.
Qed.
