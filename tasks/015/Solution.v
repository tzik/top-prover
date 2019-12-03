Require Import Problem Permutation List.

Theorem solution: task.
Proof.
  unfold task.
  intros.
  induction l.
  - apply Permutation_length_1.
    auto.
  - apply IHl; clear IHl.
    specialize (perm_swap a0 b l); intro.
    specialize (Permutation_trans H H0); intro.
    clear H H0.
    apply Permutation_sym in H1.
    specialize (perm_swap a0 a l); intro.
    specialize (Permutation_trans H1 H); intro; clear H H1.
    apply Permutation_cons_inv in H0.
    apply Permutation_sym.
    auto.
Qed.
