Require Import Problem Omega.

Theorem solution: task.
Proof.
  unfold task.
  intros m n; revert m.
  induction n; intros.
  - inversion H.
  - assert (S (S m) < n \/ S m = n \/ S (S m) = n) by omega.
    destruct H0.
    * specialize (IHn (S m) H0).
      replace (m + S n) with (S m + n) by omega.
      omega.
    * destruct H0.
      + subst n; clear H IHn.
        replace (m + S (S m)) with (S m * 2) by omega.
        rewrite Nat.div_mul; omega.
      + subst n; clear H IHn.
        replace (m + S (S (S m))) with (1 + S m * 2) by omega.
        rewrite Nat.div_add; simpl; omega.
Qed.
