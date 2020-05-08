Require Import Problem Omega.

Lemma diag : forall j, visit j j.
Proof.
  induction j; [constructor|].
  apply visit_down; [omega|].
  assert (forall i, visit i j -> visit i (S j)).
  - induction i; intros.
    * apply (visit_right j); [omega|auto].
    * apply visit_down.
      + inversion_clear H.
        omega.
      + apply IHi.
        inversion_clear H.
        auto.
  - apply H.
    auto.
Qed.

Theorem solution : task.
Proof.
  unfold task.
  induction i; intros.
  - induction j; [constructor|].
    apply (visit_right j); [auto|apply diag].
  - assert (i < j \/ i = j \/ S i = j) by omega.
    destruct H0; [|destruct H0].
    * refine (visit_down _ _ H0 _).
      apply IHi.
      omega.
    * apply visit_down; [|apply IHi]; omega.
    * subst j.
      apply diag.
Qed.
