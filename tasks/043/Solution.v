Require Import Problem Omega Lia.

Lemma even_odd : forall n, exists m, n = 2 * m \/ n = 2 * m + 1.
Proof.
  induction n; [exists 0; auto|].
  destruct IHn as [m].
  destruct H; [exists m; right|exists (S m); left]; omega.
Qed.

Theorem solution: task.
Proof.
  unfold task.
  intros.
  destruct (even_odd x) as [a].
  destruct (even_odd y) as [b].
  destruct H; destruct H0; subst x y; lia.
Qed.
