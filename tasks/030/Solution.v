Require Import Problem PeanoNat Omega.

Theorem solution : task.
Proof.
  unfold task.
  intro.
  remember n as m.
  assert (m <= n) by omega; clear Heqm.
  revert m H.

  induction n; intros.
  - apply Nat.le_0_r in H; subst m; auto.
  - do 2 (destruct m; [auto|]).
    simpl.
    rewrite IHn; omega.
Qed.
