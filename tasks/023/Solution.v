Require Import Problem PeanoNat Omega.

Lemma lsb : forall n, exists k, n = 2 * k \/ n = 2 * k + 1.
Proof.
  induction n; [exists 0; auto|].
  destruct IHn.
  destruct H; subst n; [exists x | exists (x + 1)]; omega.
Qed.

Theorem solution : task.
Proof.
  unfold task; unfold is_expressible_in_binary_notation.
  intro.
  remember n as m.
  assert (m <= n) by omega; clear Heqm.
  revert m H.
  induction n; intros.
  - apply Nat.le_0_r in H; subst m; constructor.
  - destruct m; [constructor|].
    destruct (lsb (S m)).
    destruct H0; rewrite H0; constructor; apply IHn; omega.
Qed.
