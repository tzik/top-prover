Require Export Arith.

Section Binsearch_def.

Variable f : nat -> bool.

Definition downward_closed :=
  forall m n, m <= n -> f n = true -> f m = true.

(* k: an extra parameter to convince termination checker *)
Fixpoint binsearch l r k :=
  match S l =? r with
  | true => l
  | false =>
    match k with
    | 0 => r
    | S k' =>
      let m := (l + r) / 2 in
      if f m then binsearch m r k' else binsearch l m k'
    end
  end.

End Binsearch_def.

Definition task :=
  forall f,
    downward_closed f ->
    forall l r,
      l < r -> f l = true -> f r = false ->
      exists k, forall n, f n = true <-> n <= binsearch f l r k.
