Require Import Problem.

Theorem solution: task.
Proof.
  unfold task.
  intros; split; intros.
  inversion_clear H.
  inversion H1; subst k0 l0 i; clear H1.
  inversion_clear H0.
  inversion H; subst k0 k l0; clear H.
  inversion_clear H1.
  repeat (split; auto).

  destruct H; subst k.
  destruct H0; subst l.
  destruct H0; subst j.
  destruct H0; subst m.
  destruct H0; subst i n.
  refine (po_node _ _ _ _ _ _ _).
  refine (po_node _ _ _ _ _ _ _).
  refine (po_leaf _).
  refine (po_leaf _).
  refine (po_leaf _).
Qed.
