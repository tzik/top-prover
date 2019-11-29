Require Import Problem Omega.

Lemma lemma : forall l1 l2 a b,
    prefix_sum (a + b) (plus_list l1 l2) =
    plus_list (prefix_sum a l1) (prefix_sum b l2).
Proof.
  induction l1.
  destruct l2; simpl; auto.
  destruct l2.
  simpl.
  destruct l1; simpl; auto.
  simpl.
  intros.
  rewrite <- (IHl1 l2 (a0 + a) (b + n)).
  replace (a0 + b + (a + n)) with (a0 + a + (b + n)).
  auto.
  omega.
Qed.

Theorem solution: task.
Proof.
  unfold task.
  intros.
  exact (lemma l1 l2 0 0).
Qed.
