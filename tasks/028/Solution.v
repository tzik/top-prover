Require Import Problem PeanoNat Nat.

Lemma plus_decomp (m n : nat) (f : nat -> nat) (x : nat)
  : iter (m + n) f x = iter m f (iter n f x).
Proof.
  induction m; simpl; auto.
Qed.

Lemma mult_decomp (m n : nat) (f : nat -> nat) (x : nat)
  : iter (m * n) f x = iter m (iter n f) x.
Proof.
  induction m; simpl; [auto|].
  rewrite plus_decomp; auto.
Qed.

Lemma beta (n y : nat) (f g : nat -> nat)
  : (forall x, f x = g x) -> iter n f y = iter n g y.
Proof.
  intros.
  induction n; [auto|].
  simpl; rewrite IHn; auto.
Qed.

Theorem solution: task.
Proof.
  unfold task.
  induction n; [auto|].
  intros; simpl.
  rewrite mult_decomp.
  apply beta.
  auto.
Qed.
