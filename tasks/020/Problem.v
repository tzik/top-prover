Require Import List.
Import ListNotations.

(*
  They are 2 types of solutions of https://atcoder.jp/contests/abc116/tasks/abc116_c
*)

Inductive compute1 : list nat -> nat -> Prop :=
  | c1_nil : compute1 nil 0
  | c1_app l1 l2 n m : compute1 l1 n -> compute1 l2 m -> compute1 (l1 ++ [0] ++ l2) (n + m)
  | c1_succ h t n : compute1 (h :: t) n -> compute1 (S h :: map (fun x => S x) t) (S n).

Fixpoint compute2 (l : list nat) : nat :=
  match l with
  | nil => 0
  | h1 :: t =>
    match t with
    | nil => h1
    | h2 :: t' => h1 - min h1 h2 + compute2 t
    end
  end.

Definition task := forall l, compute1 l (compute2 l).
