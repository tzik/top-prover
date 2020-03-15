Require Import Problem.

Theorem solution: task.
Proof.
  unfold task.
  intros.
  split; intros.
  inversion_clear H.
  inversion H0; subst m0 t1 t2 k0 l0; clear H0.
  inversion H6; subst k0 k l1; clear H6.
  split; [auto|].
  inversion H7; subst k l j; clear H7.
  split; [auto|].
  split; [auto|].
  inversion_clear H1.
  auto.

  destruct H; subst k.
  destruct H0; subst l.
  destruct H0; subst j.
  destruct H0; subst m.
  destruct H0; subst i n.
  refine (po_node (Node 2 (Leaf 0) (Leaf 1)) (Leaf 3) 0 3 4 _ _).
  refine (po_node (Leaf 0) (Leaf 1) 0 1 2 _ _).
  apply po_leaf.
  apply po_leaf.
  apply po_leaf.
Qed.
