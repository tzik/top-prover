Require Import Problem ZArith ZArith.Znumtheory.

Theorem solution : task.
Proof.
  unfold Problem.task.
  intros.
  unfold Square; unfold Square in H2.
  remember (Z.sqrt (n * m)) as k.
  remember (Z.gcd k m) as x.
  remember (Z.gcd k n) as y.
  apply (proj2 (Zgcd_1_rel_prime n m)) in H1.

  assert (y * k = n * x).
  subst x y.
  rewrite <- Z.gcd_mul_mono_l_nonneg.
  rewrite <- Z.gcd_mul_mono_r_nonneg.
  rewrite H2.
  rewrite Z.gcd_comm.
  auto.
  subst k; apply Z.sqrt_nonneg.
  omega.

  assert (Z.gcd x y = 1).
  subst x y.
  rewrite <- Z.gcd_assoc.
  rewrite (Z.gcd_comm m).
  rewrite <- Z.gcd_assoc.
  rewrite H1.
  repeat rewrite Z.gcd_1_r.
  auto.

  assert (n = y * Z.gcd k n).
  rewrite <- Z.gcd_mul_mono_l_nonneg.
  rewrite H3; clear H3.
  rewrite Z.mul_comm.
  rewrite Z.gcd_mul_mono_r_nonneg.
  rewrite H4; clear H4.
  omega.
  omega.
  subst y; apply Z.gcd_nonneg.

  rewrite <- Heqy in H5.
  replace (Z.sqrt n) with y.
  auto.

  specialize (Z.gcd_nonneg k n); intro.
  rewrite <- Heqy in H6.
  rewrite <- (Z.sqrt_square y H6).
  subst n; auto.
Qed.
