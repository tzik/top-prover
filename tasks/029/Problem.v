Require Import Relations.

Parameter A : Set.
Parameter R : relation A.
Axiom R_refl : reflexive A R.
Axiom R_trans : transitive A R.

Notation "x <= y" := (R x y).

Definition task :=
  forall x y, x <= y <-> forall z, (y <= z -> x <= z).
