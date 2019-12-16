Require Import Problem PeanoNat List Omega Permutation.
Import ListNotations.

Fixpoint sorted (xs : list nat) :=
  match xs with
  | nil => True
  | x :: ys =>
    match ys with
    | nil => True
    | y :: zs => x <= y /\ sorted ys
    end
  end.

Definition all (P : nat -> Prop) (xs : list nat) := fold_right and True (map P xs).
Definition upper_bound (n : nat) := all (fun x => x <= n).
Definition lower_bound (n : nat) := all (fun x => n <= x).

Lemma perm_dig : forall x xs ys, Permutation (A:=nat) (x :: xs) ys -> exists zs ws, ys = zs ++ x :: ws.
Proof.
  intros.
  assert (In x ys) by (refine (Permutation_in _ H _); simpl; auto); clear H.
  induction ys; [inversion H0|].
  simpl in H0.
  destruct H0; [subst a; exists nil; exists ys; auto|].
  apply IHys in H; clear IHys.
  destruct H; destruct H.
  exists (a :: x0); exists x1.
  subst ys.
  auto.
Qed.

Lemma perm_all : forall P xs, all P xs -> forall ys, Permutation xs ys -> all P ys.
Proof.
  induction xs; intros.
  - apply Permutation_nil in H0.
    subst ys; simpl; auto.
  - unfold all in H; simpl in H; fold (all P xs) in H.
    destruct H.
    specialize (IHxs H1); clear H1.
    destruct (perm_dig a xs ys H0); destruct H1.
    subst ys.
    assert (Permutation (a :: x ++ x0) (x ++ a :: x0)) by apply Permutation_middle.
    apply Permutation_sym in H1.
    assert (Permutation (a :: xs) (a :: x ++ x0)).
    * apply (Permutation_trans H0 H1); clear H1.
    * apply Permutation_cons_inv in H2.
      apply IHxs in H2.
      clear IHxs H1 H0.
      induction x.
      + unfold all; simpl; fold (all P x0).
        simpl in H2.
        auto.
      + unfold all; simpl; fold (all P (x ++ a :: x0)).
        unfold all in H2; simpl in H2; fold (all P (x ++ x0)) in H2.
        destruct H2.
        auto.
Qed.

Lemma perm_upper : forall n xs, upper_bound n xs -> forall ys, Permutation xs ys -> upper_bound n ys.
Proof.
  intro.
  unfold upper_bound.
  apply (perm_all (fun x => x <= n)).
Qed.

Lemma perm_lower : forall n xs, lower_bound n xs -> forall ys, Permutation xs ys -> lower_bound n ys.
Proof.
  intro.
  unfold lower_bound.
  apply (perm_all (fun x => n <= x)).
Qed.

Lemma sorted_app : forall xs n ys, upper_bound n xs -> lower_bound n ys -> sorted xs -> sorted ys -> sorted (xs ++ [n] ++ ys).
Proof.
  intros.
  induction xs; simpl.
  - destruct ys; [auto|].
    destruct H0; split; auto.
  - destruct H.
    destruct xs.
    * simpl.
      clear H3 H1; simpl in IHxs; specialize (IHxs I I).
      split; auto.
    * simpl; simpl in IHxs; simpl in H1.
      destruct H1.
      split; [auto|].
      fold (all (fun x : nat => x <= n) (n0 :: xs)) in H3.
      fold (upper_bound n (n0 :: xs)) in H3.
      apply IHxs; auto.
Qed.

Lemma filter_short (P : nat -> bool) : forall xs, length (filter P xs) <= length xs.
Proof.
  induction xs; simpl; [auto|].
  destruct (P a); simpl; omega.
Qed.

Lemma move_to_left (x :nat) (ys zs : list nat) : Permutation (x :: ys ++ zs) (ys ++ x :: zs).
Proof.
  replace (x :: ys ++ zs) with (([x] ++ ys) ++ zs) by auto.
  replace (ys ++ x :: zs) with ((ys ++ [x]) ++ zs) by (rewrite <- app_assoc; auto).
  apply Permutation_app_tail.
  apply Permutation_app_comm.
Qed.

Lemma filter_split (P Q : nat -> bool) : (forall x, P x = negb (Q x)) -> forall xs, Permutation xs (filter P xs ++ filter Q xs).
Proof.
  intros.
  induction xs; simpl; [constructor|].
  specialize (H a).
  destruct (Q a); rewrite H; simpl; [|apply perm_skip; auto].
  apply (perm_skip a) in IHxs.
  refine (Permutation_trans IHxs _).
  apply Permutation_middle.
Qed.

Definition lt_n (n : nat) := fun x => x <? n.
Definition ge_n (n : nat) := fun x => n <=? x.
Definition le_n (n : nat) := fun x => x <=? n.
Definition gt_n (n : nat) := fun x => n <? x.

Lemma lt_upper : forall n xs, upper_bound n (filter (lt_n n) xs).
Proof.
  unfold upper_bound; unfold all.
  induction xs; simpl; [auto|].
  unfold lt_n.
  assert (a < n \/ a >= n) by omega.
  destruct H.
  assert (a <? n = true) by (apply Nat.ltb_lt; auto).
  rewrite H0.
  simpl.
  split; [omega|auto].
  apply Nat.ltb_ge in H.
  rewrite H.
  auto.
Qed.

Lemma le_upper : forall n xs, upper_bound n (filter (le_n n) xs).
Proof.
  unfold upper_bound; unfold all.
  induction xs; simpl; [auto|].
  unfold le_n.
  assert (a <= n \/ a > n) by omega.
  destruct H.
  assert (a <=? n = true) by (apply Nat.leb_le; auto).
  rewrite H0.
  simpl.
  split; [omega|auto].
  apply Nat.leb_gt in H.
  rewrite H.
  auto.
Qed.

Lemma ge_lower : forall n xs, lower_bound n (filter (ge_n n) xs).
Proof.
  unfold lower_bound; unfold all.
  induction xs; simpl; [auto|].
  unfold ge_n.
  assert (n <= a \/ n > a) by omega.
  destruct H.
  assert (n <=? a = true) by (apply Nat.leb_le; auto).
  rewrite H0.
  simpl.
  split; [omega|auto].
  apply Nat.leb_gt in H.
  rewrite H.
  auto.
Qed.

Lemma gt_lower : forall n xs, lower_bound n (filter (gt_n n) xs).
Proof.
  unfold lower_bound; unfold all.
  induction xs; simpl; [auto|].
  unfold gt_n.
  assert (n < a \/ n >= a) by omega.
  destruct H.
  assert (n <? a = true) by (apply Nat.ltb_lt; auto).
  rewrite H0.
  simpl.
  split; [omega|auto].
  apply Nat.ltb_ge in H.
  rewrite H.
  auto.
Qed.

Lemma sort_mid : forall x ys z ws, sorted (x :: ys ++ z :: ws) -> x <= z.
Proof.
  induction ys; simpl; intros.
  destruct H; auto.
  destruct H.
  destruct ys.
  simpl in H0; simpl in IHys.
  destruct H0.
  omega.
  simpl in IHys.
  simpl in H0.
  apply (IHys z ws).
  destruct H0.
  split; [omega|auto].
Qed.

Lemma qs1_split : forall n xs, Permutation xs (filter (lt_n n) xs ++ filter (ge_n n) xs).
Proof.
  intros.
  apply filter_split.
  intros.
  unfold lt_n; unfold ge_n.
  apply Nat.ltb_antisym.
Qed.

Lemma qs2_split : forall n xs, Permutation xs (filter (le_n n) xs ++ filter (gt_n n) xs).
Proof.
  intros.
  apply filter_split.
  intros.
  unfold le_n; unfold gt_n.
  apply Nat.leb_antisym.
Qed.

Lemma qs1_perm : forall xs ys, quicksort1 xs ys -> Permutation xs ys.
Proof.
  intro.
  remember (length xs) as k.
  assert (length xs <= k) by omega; clear Heqk.
  revert xs H.
  induction k; intros.
  - apply Nat.le_0_r in H.
    apply length_zero_iff_nil in H.
    subst xs.
    inversion H0; constructor.
  - destruct xs; [inversion H0; constructor|].
    simpl in H.
    assert (length xs <= k) by omega; clear H.
    inversion H0; clear H0.
    subst head tail ys.
    refine (Permutation_trans _ (move_to_left n l r)).
    apply perm_skip.
    fold (lt_n n) in H3; fold (ge_n n) in H5.
    refine (Permutation_trans (qs1_split n xs) _).
    remember (filter (lt_n n) xs) as xs_l.
    remember (filter (ge_n n) xs) as xs_r.
    refine (Permutation_app _ _); (apply IHk; [|auto]).
    assert (length xs_l <= length xs) by (subst xs_l; apply filter_short); omega.
    assert (length xs_r <= length xs) by (subst xs_r; apply filter_short); omega.
Qed.


Lemma qs2_perm : forall xs ys, quicksort2 xs ys -> Permutation xs ys.
Proof.
  intro.
  remember (length xs) as k.
  assert (length xs <= k) by omega; clear Heqk.
  revert xs H.
  induction k; intros.
  - apply Nat.le_0_r in H.
    apply length_zero_iff_nil in H.
    subst xs.
    inversion H0; constructor.
  - destruct xs; [inversion H0; constructor|].
    simpl in H.
    assert (length xs <= k) by omega; clear H.
    inversion H0; clear H0.
    subst head tail ys.
    refine (Permutation_trans _ (move_to_left n l r)).
    apply perm_skip.
    fold (le_n n) in H3; fold (gt_n n) in H5.
    refine (Permutation_trans (qs2_split n xs) _).
    remember (filter (le_n n) xs) as xs_l.
    remember (filter (gt_n n) xs) as xs_r.
    refine (Permutation_app _ _); (apply IHk; [|auto]).
    assert (length xs_l <= length xs) by (subst xs_l; apply filter_short); omega.
    assert (length xs_r <= length xs) by (subst xs_r; apply filter_short); omega.
Qed.

Lemma qs1_sorted : forall xs ys, quicksort1 xs ys -> sorted ys.
Proof.
  intro.
  remember (length xs) as k.
  assert (length xs <= k) by omega; clear Heqk.
  revert xs H.
  induction k; intros.
  apply Nat.le_0_r in H.
  apply length_zero_iff_nil in H.
  subst xs; inversion H0; simpl; auto.
  destruct xs; [inversion H0; simpl; auto|].
  simpl in H; assert (length xs <= k) by omega; clear H.
  inversion H0; clear H0.
  subst head tail ys.
  fold (lt_n n) in H3; fold (ge_n n) in H5.
  remember (filter (lt_n n) xs) as xs_l.
  remember (filter (ge_n n) xs) as xs_r.
  apply sorted_app.
  apply qs1_perm in H3.
  apply (perm_upper n xs_l); [|auto].
  subst xs_l; apply lt_upper.
  apply qs1_perm in H5.
  apply (perm_lower n xs_r); [|auto].
  subst xs_r; apply ge_lower.
  apply (IHk xs_l); [|auto].
  assert (length xs_l <= length xs) by (subst xs_l; apply filter_short); omega.
  apply (IHk xs_r); [|auto].
  assert (length xs_r <= length xs) by (subst xs_r; apply filter_short); omega.
Qed.

Lemma qs2_sorted : forall xs ys, quicksort2 xs ys -> sorted ys.
Proof.
  intro.
  remember (length xs) as k.
  assert (length xs <= k) by omega; clear Heqk.
  revert xs H.
  induction k; intros.
  apply Nat.le_0_r in H.
  apply length_zero_iff_nil in H.
  subst xs; inversion H0; simpl; auto.
  destruct xs; [inversion H0; simpl; auto|].
  simpl in H; assert (length xs <= k) by omega; clear H.
  inversion H0; clear H0.
  subst head tail ys.
  fold (le_n n) in H3; fold (gt_n n) in H5.
  remember (filter (le_n n) xs) as xs_l.
  remember (filter (gt_n n) xs) as xs_r.
  apply sorted_app.
  apply qs2_perm in H3.
  apply (perm_upper n xs_l); [|auto].
  subst xs_l; apply le_upper.
  apply qs2_perm in H5.
  apply (perm_lower n xs_r); [|auto].
  subst xs_r; apply gt_lower.
  apply (IHk xs_l); [|auto].
  assert (length xs_l <= length xs) by (subst xs_l; apply filter_short); omega.
  apply (IHk xs_r); [|auto].
  assert (length xs_r <= length xs) by (subst xs_r; apply filter_short); omega.
Qed.

Lemma sort_uniq : forall xs ys, Permutation xs ys -> sorted xs -> sorted ys -> xs = ys.
Proof.
  induction xs; simpl; intros.
  apply Permutation_nil in H.
  auto.
  assert (lower_bound a (a :: xs)).
  clear H IHxs H1 ys.
  unfold lower_bound; unfold all.
  simpl; split; [omega|].
  induction xs.
  auto.
  simpl.
  destruct H0.
  split; [auto|].
  apply IHxs; clear IHxs.
  destruct xs; [auto|].
  destruct H0.
  split; [omega|auto].

  assert (lower_bound a ys).
  refine (perm_lower _ _ H2 _ H).
  clear H2.

  destruct (perm_dig a _ _ H); destruct H2.
  subst ys.
  destruct x.
  simpl.
  f_equal.
  apply IHxs.
  simpl in H.
  apply Permutation_cons_inv in H.
  auto.
  destruct xs.
  auto.
  destruct H0.
  auto.
  simpl in H1.
  destruct x0.
  auto.
  destruct H1.
  auto.

  assert (a <= n).
  unfold lower_bound in H3; unfold all in H3; destruct H3; auto.
  rewrite <- app_comm_cons in H1.
  assert (n <= a) by (apply sort_mid in H1; auto).
  assert (n = a) by omega; clear H2 H4.
  subst n.
  simpl.
  f_equal.
  apply IHxs.
  simpl in H.
  apply Permutation_cons_inv in H; auto.
  destruct xs.
  auto.
  destruct H0.
  auto.
  remember (x ++ a :: x0) as t.
  simpl in H1.
  destruct t.
  auto.
  destruct H1.
  auto.
Qed.

Theorem solution : task.
Proof.
  unfold task.
  intros.
  apply sort_uniq.
  - apply qs1_perm in H.
    apply qs2_perm in H0.
    apply Permutation_sym in H.
    apply (Permutation_trans H H0).
  - apply qs1_sorted in H; auto.
  - apply qs2_sorted in H0; auto.
Qed.
