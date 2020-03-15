Definition eventually_periodic (f : nat -> nat) (n : nat) : Prop :=
  exists t m0,
    t > 0 /\ forall m, m0 < m -> Nat.iter (t + m) f n = Nat.iter m f n.

(* Floyd's tortoise and hare algorithm *)
Inductive hare_catches_tortoise (f : nat -> nat) : nat -> nat -> Prop :=
| CatchNext : forall x y, x = f y -> hare_catches_tortoise f x y
| CatchLater : forall x y, hare_catches_tortoise f (f x) (f (f y)) ->
                           hare_catches_tortoise f x y.

Definition task :=
  forall f n, eventually_periodic f n <-> hare_catches_tortoise f n (f n).
