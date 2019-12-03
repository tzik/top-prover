Require Import Nat.

Definition task :=
  forall (f : nat -> nat) (n m x : nat),
    iter (m^n) (A:=nat) f x = iter n (A:=nat->nat) (iter m (A:=nat)) f x.
