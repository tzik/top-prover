Require Import Problem PeanoNat Omega.

Lemma lsb : forall n, exists k, n = 2 * k \/ n = 2 * k + 1.
Proof.
  induction n.
  exists 0.
  auto.

  destruct IHn.
  destruct H; subst n.
  exists x.
  omega.

  exists (x + 1).
  omega.
Qed.

Lemma lemma : forall m n, n <= m -> is_expressible_in_binary_notation n.
Proof.
  induction m; intros.
  rewrite Nat.le_0_r in H.
  subst n.
  constructor.

  specialize (lsb n); intro.
  destruct H0; destruct H0; subst n; constructor; apply IHm; clear IHm; omega.
Qed.

Theorem solution : task.
Proof.
  unfold Problem.task.
  intro.
  exact (lemma n n (Nat.le_refl n)).
Qed.
