Require Import Problem.

Definition failcase (n : nat) : bool := negb (Problem.f n n).

Theorem solution : task.
Proof.
  unfold task.
  specialize (f_surjective failcase).
  intros.
  destruct H.
  unfold NtoB_eqv in H.
  unfold failcase in H.
  specialize (H x).
  remember (f x x).
  clear Heqb x.
  destruct b; discriminate.
Qed.
