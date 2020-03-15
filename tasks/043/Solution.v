Require Import Problem Omega Lia.

Lemma lemma : forall n, exists m, n = 2 * m \/ n = 2 * m + 1.
Proof.
  intros.
  induction n.
  exists 0.
  auto.
  destruct IHn.
  destruct H.
  rewrite H.
  exists x.
  right.
  omega.
  rewrite H.
  exists (S x).
  left.
  omega.
Qed.

Lemma lemma2 : forall m n i, i < 4 -> 4 * m + i = 4 * n -> i = 0.
Proof.
  induction m; intros; omega.
Qed.

Lemma lemma3 : forall x, (2 * x) * (2 * x) = 4 * x * x.
Proof.
  intros.
  lia.
Qed.

Theorem solution: task.
Proof.
  unfold task.
  intros.
  destruct (lemma x).
  destruct H; subst x; rename x0 into x.
  destruct (lemma y).
  destruct H; subst y; rename x0 into y.
  all: intro.
  lia.
  lia.
  destruct (lemma y).
  destruct H0; subst y; rename x0 into y.
  lia.
  lia.
Qed.
