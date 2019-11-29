Require Import Problem PeanoNat Omega.

Lemma lemma : forall m n, n <= m -> double n = 2 * n.
Proof.
  induction m; intros.
  specialize (Nat.le_0_r n); intro.
  destruct H0.
  rewrite (H0 H).
  simpl.
  omega.

  destruct n. simpl. omega.
  destruct n. simpl. omega.

  remember (2 * S (S n)) as k.
  simpl.

  assert (n <= m).
  omega.
  rewrite (IHm n H0).
  subst k.
  omega.
Qed.

Theorem solution : task.
Proof.
  unfold Problem.task.
  intro.
  exact (lemma n n (Nat.le_refl n)).
Qed.
