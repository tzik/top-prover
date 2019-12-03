Require Import List Nat.
Import ListNotations.

Fixpoint list_in (l: list nat) (n: nat) :=
  match l with
  | [] => false
  | h :: t =>
    match Nat.eqb n h with
    | true => true
    | false => list_in t n
    end
  end.

Fixpoint unique (l: list nat) :=
  match l with
  | [] => []
  | h :: t =>
    match list_in t h with
    | true => unique t
    | false => h :: unique t
    end
  end.

Definition task := forall l, unique (unique l) = unique l.
