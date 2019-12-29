Require Import Problem PeanoNat Omega.

Theorem solution : task.
Proof.
  unfold task.
  intros.
  do 2 (try destruct m; try destruct n; try omega).
  simpl in H.
  rewrite Nat.add_comm in H.
  inversion H.
Qed.
