Require Import Problem PeanoNat Omega Lia.

Lemma Snth_first : Snth 0 (gen 0 0) = 0.
Proof.
  auto.
Qed.

Lemma Snth_down : forall i j k, i < j -> Snth (S k) (gen i j) = Snth k (gen (S i) j).
Proof.
  intros.
  apply Nat.ltb_lt in H.
  simpl.
  rewrite H.
  auto.
Qed.

Lemma Snth_right : forall i j k, i >= j -> Snth (S k) (gen i j) = Snth k (gen 0 (S j)).
Proof.
  intros.
  apply Nat.ltb_ge in H.
  simpl.
  rewrite H.
  auto.
Qed.

Lemma Snth_shift : forall i j k, i <= j -> Snth (k + S j) (gen i j) = Snth k (gen i (S j)).
Proof.
  induction i; intros.
  rewrite <- (Snth_right j); [|omega].
  replace (k + S j) with (S k + j) by omega.
  remember (S k) as k'; clear k Heqk'.
  assert (forall i, i <= j -> Snth (k' + i) (gen (j - i) j) = Snth k' (gen j j)).
  induction i; intros.
  replace (k' + 0) with k' by omega.
  replace (j - 0) with j by omega.
  auto.

  replace (k' + S i) with (S (k' + i)) by omega.
  rewrite Snth_down; [|omega].
  replace (S (j - S i)) with (j - i) by omega.
  apply IHi.
  omega.

  rewrite <- (H0 j); [|omega].
  replace (j - j) with 0 by omega.
  auto.

  rewrite <- Snth_down; [|omega].
  rewrite <- Snth_down; [|omega].
  rewrite <- IHi; [|omega].
  auto.
Qed.

Fixpoint accum m n :=
  match n with
  | 0 => 0
  | S n' => if m <? n then S n' + accum m n' else 0
  end.

Lemma accum_diag : forall n, accum n n = 0.
Proof.
  destruct n; simpl; [auto|].
  assert (S n >= S n) by omega.
  apply Nat.ltb_ge in H.
  rewrite H; clear H.
  auto.
Qed.

Lemma accum_extract_l : forall m n, m < n -> accum m n = accum (S m) n + S m.
Proof.
  intros.
  remember (n - m) as k.
  revert m n Heqk H.
  induction k; intros; [omega|].
  destruct n; [omega|].
  simpl.
  assert (m = n \/ m < n) by omega.
  destruct H0.
  subst m.
  clear k Heqk IHk.
  rewrite accum_diag.
  apply Nat.ltb_lt in H.
  rewrite H; clear H.
  assert (S n >= S n) by omega.
  apply Nat.ltb_ge in H.
  rewrite H; clear H.
  omega.
  rewrite IHk; [|omega|omega].
  apply Nat.ltb_lt in H.
  rewrite H; clear H.
  assert (S m < S n) by omega.
  apply Nat.ltb_lt in H.
  rewrite H; clear H.
  omega.
Qed.

Theorem solution : task.
Proof.
  unfold task.
  intros.
  exists (accum 0 (x + y) + x).
  split.
  assert (y <= x + y) by omega.
  refine (le_trans _ _ _ H _); clear H.
  remember (x + y) as z.
  clear y Heqz.
  assert (accum 0 z <= accum 0 z + x) by omega.
  refine (le_trans _ _ _ _ H); clear x H.
  destruct z; simpl; omega.

  remember (x + y) as z.
  assert (forall i, i <= z -> Snth (accum i z + x) (gen 0 i) = Snth (accum 0 z + x) (gen 0 0)).
  induction i; intros; [auto|].
  rewrite <- Snth_shift; [|omega].
  replace (accum (S i) z + x + S i) with (accum i z + x); [apply IHi; omega|].
  rewrite accum_extract_l; omega.
  rewrite <- (H z); [|omega].
  clear H.
  rewrite accum_diag; simpl.
  assert (x <= z) by omega; clear y Heqz.

  assert (forall i, i <= x -> Snth (x - i) (gen i z) = Snth x (gen 0 z)).
  induction i; intros.
  replace (x - 0) with x by omega.
  auto.

  rewrite <- Snth_down; [|omega].
  replace (S (x - S i)) with (x - i) by omega.
  rewrite IHi; omega.

  rewrite <- (H0 x); [|omega].
  replace (x - x) with 0 by omega.
  auto.
Qed.
