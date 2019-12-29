Require Import Problem Omega Znumtheory.
Import ZArith.Zdiv.

Lemma prime_not_0 : forall p, prime p -> p <> 0.
Proof.
  intros.
  contradict H.
  subst p.
  apply not_prime_0.
Qed.

Lemma zero_factor (p a b : Z) : prime p -> (a * b) mod p = 0 -> a mod p = 0 \/ b mod p = 0.
Proof.
  intros.
  assert (p <> 0) by (apply prime_not_0; auto).
  apply (Zmod_divide (a * b) p H1) in H0; clear H1.
  apply (prime_mult p H) in H0.
  destruct H0; apply Zdivide_mod in H0; auto.
Qed.

Lemma transpose (p a b : Z) : p > 0 -> a mod p = b mod p -> (a - b) mod p = 0.
Proof.
  intros.
  rewrite (Zmod_eq a p H) in H0.
  rewrite (Zmod_eq b p H) in H0.
  assert (forall x y z w : Z, x - z = y - w -> x - y = z - w) by (intros; omega).
  apply (H1 a b (a / p * p) (b / p * p)) in H0; clear H1.
  rewrite <- Z.mul_sub_distr_r in H0.
  rewrite H0.
  apply Z_mod_mult.
Qed.

Theorem solution: task.
Proof.
  unfold task.
  intros.
  destruct H0; destruct H1; destruct H2.
  apply transpose in H3; [|omega].
  rewrite <- Z.mul_sub_distr_r in H3.
  apply zero_factor in H3; [|auto].
  destruct H3.
  - assert (0 <= k1 - k2 < p \/ 0 <= k2 - k1 < p) by omega.
    destruct H7.
    * rewrite Zmod_small in H3; omega.
    * apply Z_mod_zero_opp_full in H3.
      rewrite Zmod_small in H3; omega.
  - rewrite Zmod_small in H3; omega.
Qed.
