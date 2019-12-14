Require Import Problem PeanoNat Omega.

Lemma lemma (n : nat) (l : list nat) : list_in l n = false -> List.count_occ Nat.eq_dec l n = 0.
Proof.
  induction l; simpl; [auto|].
  destruct (Nat.eq_dec a n).
  - subst a.
    rewrite Nat.eqb_refl.
    discriminate.
  - apply Nat.neq_sym in n0.
    apply Nat.eqb_neq in n0.
    rewrite n0.
    auto.
Qed.

Lemma lemma2 (l : list nat) (n : nat) : list_in l n = false -> list_in (unique l) n = false.
Proof.
  induction l; simpl; [auto|].
  destruct (Nat.eq_dec n a).
  - subst n.
    rewrite Nat.eqb_refl.
    discriminate.
  - apply Nat.eqb_neq in n0.
    rewrite n0.
    destruct (list_in l a); [auto|].
    simpl.
    rewrite n0.
    auto.
Qed.

Theorem solution : task.
Proof.
  unfold Problem.task.
  intros.
  induction l; simpl; [discriminate|].
  destruct (Nat.eq_dec n a).
  - subst n.
    clear H.
    remember (list_in l a) as b.
    destruct b; [auto|].
    clear IHl.
    simpl.
    destruct (Nat.eq_dec a a).
    f_equal.
    rewrite lemma.
    auto.
    apply lemma2.
    auto.
    contradict n.
    auto.
  - simpl in H.
    specialize (proj2 (Nat.eqb_neq n a) n0); intro.
    rewrite H0 in H.
    specialize (IHl H).
    destruct (list_in l a); [auto|].
    simpl.
    destruct (Nat.eq_dec a n); [contradict n0|]; auto.
Qed.
