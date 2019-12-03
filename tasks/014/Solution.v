Require Import Problem PeanoNat Omega.

Lemma binary (n : nat) : mod2 n = 0 \/ mod2 n = 1.
Proof.
  induction n.
  - auto.
  - destruct IHn; simpl; rewrite H; auto.
Qed.

Lemma add_hom (m n : nat) : mod2 (m + n) = mod2 (mod2 m + mod2 n).
Proof.
  induction m; simpl.
  - destruct (binary n); rewrite H; auto.
  - rewrite IHm; clear IHm.
    destruct (binary m); destruct (binary n).
    all: rewrite H; clear H; rewrite H0; clear H0.
    all: simpl; auto.
Qed.

Theorem solution: task.
Proof.
  unfold task.
  induction n.
  - auto.
  - simpl.
    rewrite Nat.mul_comm.
    rewrite add_hom.
    simpl.
    rewrite (add_hom n).
    rewrite <- IHn; clear IHn.
    destruct (binary n); rewrite H; auto.
Qed.
