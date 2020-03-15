Require Import Bool Arith.

Inductive bintree :=
| Leaf : nat -> bintree
| Node : nat -> bintree -> bintree -> bintree.

Inductive is_post_order : bintree -> nat -> nat -> Prop :=
| po_leaf k : is_post_order (Leaf k) k (S k)
| po_node t1 t2 k l m :
    is_post_order t1 k l -> is_post_order t2 l m ->
    is_post_order (Node m t1 t2) k (S m).

Coercion Leaf : nat >-> bintree.
Notation "[ x ; y ,  z ] " :=  (Node x y z).

Definition task :=
  forall i j k l m n : nat,
    is_post_order [i; [j; k, l], m] 0 n <->
    k = 0 /\ l = 1 /\ j = 2 /\ m = 3 /\ i = 4 /\ n = 5.
