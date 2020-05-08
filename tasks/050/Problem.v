Require Import Arith.

CoInductive stream :=
| SCons : nat -> stream -> stream.

CoFixpoint gen m n :=
  SCons m (if m <? n then gen (S m) n else gen 0 (S n)).

Fixpoint Snth n s :=
  match n with
  | 0 => match s with SCons h _ => h end
  | S n' => match s with SCons _ s' => Snth n' s' end
  end.

(* Show that each natural number occurs infinitely often in [gen 0 0]. *)
Definition task :=
  forall x, forall y, exists z, y <= z /\ Snth z (gen 0 0) = x.
