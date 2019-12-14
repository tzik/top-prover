Require Import Problem.

Definition failcase (n : nat) : bool := negb (Problem.f n n).

Theorem solution : task.
Proof.
  unfold task.
  destruct (f_surjective failcase).
  specialize (H x).
  unfold failcase in H.
  remember (f x x).
  destruct b; discriminate.
Qed.
