Require Import Problem PeanoNat Omega.

Theorem plus_assoc_proof : Problem.plus_assoc.
Proof.
  unfold Problem.plus_assoc.
  intros.
  omega.
Qed.

Theorem plus_assoc_proof_2 : Problem.plus_assoc.
Proof.
  unfold Problem.plus_assoc.
  intros.
  rewrite <- Nat.add_assoc.
  reflexivity.
Qed.

Theorem plus_assoc_proof_3 : Problem.plus_assoc.
Proof.
  unfold Problem.plus_assoc.
  induction n; simpl.
  - reflexivity.
  - intros.
    rewrite IHn.
    reflexivity.
Qed.
