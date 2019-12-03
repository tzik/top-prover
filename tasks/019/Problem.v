Require Import List PeanoNat.
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

Definition task := forall l n, list_in l n = true -> count_occ Nat.eq_dec (unique l) n = 1.
