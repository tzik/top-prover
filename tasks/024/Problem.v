Require Import ZArith Znumtheory.

Definition task :=
  forall p, prime p ->
  forall a, 1 <= a < p ->
  forall k1, 0 <= k1 < p ->
  forall k2, 0 <= k2 < p ->
  k1 * a mod p = k2 * a mod p -> k1 = k2.
