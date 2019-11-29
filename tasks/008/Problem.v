Require Import List.

Inductive quicksort1 : list nat -> list nat -> Prop :=
| Q1nil: quicksort1 nil nil
| Q1cons (head : nat) (tail l r : list nat) :
    quicksort1 (filter (fun x => Nat.ltb x head) tail) l ->
    quicksort1 (filter (fun x => Nat.leb head x) tail) r ->
    quicksort1 (head :: tail) (l ++ (cons head nil) ++ r).

Inductive quicksort2 : list nat -> list nat -> Prop :=
| Q2nil: quicksort2 nil nil
| Q2cons (head : nat) (tail l r : list nat) :
    quicksort2 (filter (fun x => Nat.leb x head) tail) l ->
    quicksort2 (filter (fun x => Nat.ltb head x) tail) r ->
    quicksort2 (head :: tail) (l ++ (cons head nil) ++ r).

Definition task :=
  forall x ret1 ret2, quicksort1 x ret1 -> quicksort2 x ret2 -> ret1 = ret2.
