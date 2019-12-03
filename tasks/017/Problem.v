Require Import List PeanoNat.

Definition task := forall l n, count_occ Nat.eq_dec l n = count_occ Nat.eq_dec (rev l) n.
