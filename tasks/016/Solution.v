Require Import Problem.

Theorem solution: task.
Proof.
  unfold task.
  intro.
  apply gcd_swap.
  apply gcd_step.
  induction n.
  - apply gcd_O.
  - apply gcd_swap.
    replace (S n) with (1 + n) by auto.
    apply gcd_step.
    apply gcd_swap.
    auto.
Qed.
