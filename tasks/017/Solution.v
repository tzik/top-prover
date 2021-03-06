Require Import Problem List PeanoNat.
Import ListNotations.

Lemma lemma : forall xs a n, count_occ Nat.eq_dec (xs ++ [a]) n = count_occ Nat.eq_dec (a :: xs) n.
Proof.
  intros.
  induction xs; [auto|].
  rewrite <- app_comm_cons.
  simpl.
  rewrite IHxs; clear IHxs.
  destruct (Nat.eq_dec a0 n); [subst a0|]; simpl.
  all: destruct (Nat.eq_dec a n); auto.
Qed.

Theorem solution: task.
Proof.
  unfold task.
  intros.
  induction l; [auto|].
  replace (rev (a :: l)) with (rev l ++ [a]) by auto.
  rewrite lemma.
  simpl.
  rewrite IHl.
  auto.
Qed.
