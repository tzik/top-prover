Inductive gcd: nat -> nat -> nat -> Prop :=
  | gcd_O n : gcd n O n
  | gcd_step n m p : gcd m n p -> gcd (n + m) n p
  | gcd_swap n m p : gcd m n p -> gcd n m p.

Example gcd_ex1 : gcd 6 4 2.
Proof.
  apply gcd_step with (n := 4).
  apply gcd_swap.
  apply gcd_step with (n := 2).
  apply gcd_step with (n := 2).
  apply gcd_swap.
  apply gcd_O.
Qed.

Definition task := forall n, gcd n (n + 1) 1.
