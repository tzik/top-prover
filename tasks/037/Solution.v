Require Import Problem.

Theorem solution: task.
Proof.
  unfold task.
  split; intros.
  - induction H; [auto|].
    inversion IHiszero.
  - subst n.
    constructor.
Qed.
