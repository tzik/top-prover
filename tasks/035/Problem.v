Definition NtoB := nat -> bool.

Definition NtoB_eqv (g h : NtoB) : Prop := forall i, g i = h i.

Parameter f : nat -> NtoB.
Axiom f_surjective : forall (g : NtoB), exists n, NtoB_eqv (f n) g.

Definition task := False.
