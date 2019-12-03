Require Import List.

Inductive tree := Leaf | Node (v : nat) (l r : tree).

Fixpoint tree_at (t : tree) (index : list bool) : option nat :=
  match t with
  | Leaf => None
  | Node v l r =>
    match index with
    | nil => Some v
    | false :: index' => tree_at l index'
    | true :: index' => tree_at r index'
    end
  end.

Definition task := forall (t t' : tree), (forall i, tree_at t i = tree_at t' i) -> t = t'.
