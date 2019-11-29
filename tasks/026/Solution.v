Require Import Problem PeanoNat.

Theorem solution : task.
Proof.
  unfold Problem.task.
  intros.
  destruct m; try destruct m; try destruct m; destruct n; try destruct n; try destruct n.
  all: simpl in H; try auto; try discriminate.

  inversion H; clear H.
  rewrite Nat.add_comm in H1.
  discriminate.

  rewrite Nat.mul_comm in H.
  discriminate.

  inversion H; clear H.
  rewrite Nat.add_comm in H1.
  discriminate.
Qed.
