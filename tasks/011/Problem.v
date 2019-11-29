Require Import List.

Inductive swap_once: list nat -> list nat -> Prop :=
| OnceSwap1: forall h1 h2 t, swap_once (h1 :: h2 :: t) (h2 :: h1 :: t)
| OnceSwap2: forall h t1 t2, swap_once t1 t2 -> swap_once (h :: t1) (h :: t2).

Inductive is_odd_permutation: list nat -> list nat -> Prop :=
| OddPermutation1: forall l1 l2,
    swap_once l1 l2 -> is_odd_permutation l1 l2
| OddPermutation2: forall l1 l2 l3 l4,
    swap_once l1 l2 -> swap_once l2 l3 -> is_odd_permutation l3 l4 ->
    is_odd_permutation l1 l4.

Definition task := forall l1 l2, NoDup l1 -> is_odd_permutation l1 l2 -> l1 <> l2.
