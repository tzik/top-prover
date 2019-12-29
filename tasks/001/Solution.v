Require Import Problem PeanoNat Omega.

Theorem plus_assoc_proof : Problem.plus_assoc.
Proof.
  unfold Problem.plus_assoc.
  intros.
  omega.
Qed.
