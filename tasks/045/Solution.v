Require Import Problem Omega Lia Nat.

Lemma iter_S_l (f : nat -> nat) (n k : nat) : iter (S k) f n = f (iter k f n).
Proof.
  auto.
Qed.

Lemma iter_S_r (f : nat -> nat) (n k : nat) : iter (S k) f n = iter k f (f n).
Proof.
  induction k; [auto|].
  simpl.
  rewrite <- IHk.
  auto.
Qed.

Lemma iter_split (f : nat -> nat) (a n k : nat) : iter (a + k) f n = iter a f (iter k f n).
Proof.
  induction a; [auto|].
  simpl.
  f_equal.
  auto.
Qed.

Lemma skip' : forall f n k, iter k f n = iter (2 * S k) f n -> forall i, i <= k -> hare_catches_tortoise f (iter (k - i) f n) (iter (2 * (k - i)) f (f n)).
Proof.
  induction i.
  replace (k - 0) with k by omega.
  intro.
  apply CatchNext.
  rewrite H; clear H H0.
  replace (2 * S k) with (S (S (2 * k))) by omega.
  rewrite iter_S_r.
  auto.
  intro.
  apply CatchLater.
  repeat rewrite <- iter_S_l.
  replace (S (S (2 * (k - S i)))) with (2 * (k - i)) by omega.
  replace (S (k - S i)) with (k - i) by omega.
  apply IHi.
  omega.
Qed.

Lemma skip : forall f n, (exists k, iter k f n = iter (2 * S k) f n) -> hare_catches_tortoise f n (f n).
Proof.
  intros.
  destruct H as [k].
  assert (k <= k) by omega.
  specialize (skip' f n k H k H0); intro.
  replace (k - k) with 0 in H1 by omega.
  simpl in H1.
  auto.
Qed.

Lemma extract : forall f n m, hare_catches_tortoise f n m -> exists k, iter k f n = iter (2 * k + 1) f m.
Proof.
  intros.
  induction H.
  exists 0.
  simpl.
  auto.
  destruct IHhare_catches_tortoise as [k].
  exists (S k).
  replace (2 * S k + 1) with (S (S (2 * k + 1))) by omega.
  repeat rewrite iter_S_r.
  auto.
Qed.

Lemma crash_point : forall t m0, t > 0 -> exists i, i * t > m0 + 2.
Proof.
  intros.
  exists (m0 + 3).
  assert (t >= 1) by omega.
  apply (Nat.mul_le_mono_l 1 t (m0 + 3)) in H0.
  omega.
Qed.

Theorem solution: task.
Proof.
  unfold task.
  unfold eventually_periodic.
  intros; split; intros.
  destruct H as [t].
  destruct H as [m0].
  destruct H.
  apply skip.
  destruct (crash_point t m0 H) as [i].
  remember (i * t - 2) as k.
  exists k.
  assert (m0 < k) by omega.
  apply H0 in H2; clear H0.
  assert (k + 2 = i * t) by omega.
  replace (2 * S k) with ((k + 2) + k) by omega.
  rewrite H0.
  clear Heqk H0 H1 m0.
  induction i; [auto|].
  replace (S i * t + k) with (i * t + (t + k)) by lia.
  rewrite iter_split.
  rewrite H2.
  rewrite <- iter_split.
  auto.

  destruct (extract f n (f n) H) as [k]; clear H.
  rewrite <- iter_S_r in H0.
  exists (k + 2); exists k.
  split; [omega|].
  intros.
  replace (S (2 * k + 1)) with (k + 2 + k) in H0 by omega.
  replace m with ((m - k) + k) by omega.
  remember (m - k) as a; clear Heqa m H.
  replace (k + 2 + (a + k)) with (a + (k + 2 + k)) by omega.
  rewrite iter_split.
  rewrite <- H0.
  rewrite iter_split.
  auto.
Qed.
