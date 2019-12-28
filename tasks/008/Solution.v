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

Lemma len_0_nil (xs : list nat) : length xs <= 0 -> xs = nil.
Proof.
  intros; apply length_zero_iff_nil; omega.
Qed.

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
    specialize (Permutation_middle x x0 a); intro.
    apply Permutation_sym in H1.
    apply (Permutation_trans H0) in H1; clear H0.
    apply Permutation_cons_inv in H1.
    apply IHxs in H1; clear IHxs.
    induction x; [simpl in H1; split; auto|].
    destruct H1.
    split; [|apply IHx]; auto.
Qed.

Lemma perm_upper : forall n xs, upper_bound n xs -> forall ys, Permutation xs ys -> upper_bound n ys.
Proof.
  intro; apply (perm_all _).
Qed.

Lemma perm_lower : forall n xs, lower_bound n xs -> forall ys, Permutation xs ys -> lower_bound n ys.
Proof.
  intro; apply (perm_all _).
Qed.

Lemma sorted_tail : forall x xs, sorted (x :: xs) -> sorted xs.
Proof.
  destruct xs; [auto|].
  intro H; destruct H.
  auto.
Qed.

Lemma sorted_app : forall xs n ys, upper_bound n xs -> lower_bound n ys ->
                                   sorted xs -> sorted ys -> sorted (xs ++ [n] ++ ys).
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

Lemma filter_short (k : nat) (xs : list nat)
  : length xs <= k -> forall P, length (filter P xs) <= k.
Proof.
  intros.
  refine (Nat.le_trans _ _ _ _ H); clear k H.
  induction xs; simpl; [auto|].
  destruct (P a); simpl; omega.
Qed.

Lemma filter_split (P Q : nat -> bool) : (forall x, P x = negb (Q x)) -> forall xs, Permutation xs (filter P xs ++ filter Q xs).
Proof.
  intros.
  induction xs; simpl; [constructor|].
  rewrite H.
  destruct (Q a); simpl; [|apply perm_skip; auto].
  apply (perm_skip a) in IHxs.
  refine (Permutation_trans IHxs _).
  apply Permutation_middle.
Qed.

Definition lt_n (n : nat) := fun x => x <? n.
Definition ge_n (n : nat) := fun x => n <=? x.
Definition le_n (n : nat) := fun x => x <=? n.
Definition gt_n (n : nat) := fun x => n <? x.

Lemma boundary : forall n xs, upper_bound n (filter (lt_n n) xs) /\
                              upper_bound n (filter (le_n n) xs) /\
                              lower_bound n (filter (gt_n n) xs) /\
                              lower_bound n (filter (ge_n n) xs).
Proof.
  unfold upper_bound; unfold lower_bound; unfold all.
  unfold lt_n; unfold le_n; unfold gt_n; unfold ge_n.
  induction xs; simpl; [auto|].
  destruct IHxs; destruct H0; destruct H1.
  assert (C: a = n \/ a > n \/ a < n) by omega.
  destruct C; [subst|destruct H3;repeat rewrite Nat.ltb_antisym]; simpl.
  rewrite Nat.ltb_irrefl; rewrite Nat.leb_refl; simpl.
  repeat split; auto.
  all: repeat rewrite (proj2 (Nat.leb_gt _ _) H3).
  all: repeat rewrite (proj2 (Nat.leb_le _ _) (Nat.lt_le_incl _ _ H3)).
  all: simpl; repeat split; auto; omega.
Qed.

Lemma sort_mid : forall x ys z ws, sorted (x :: ys ++ z :: ws) -> x <= z.
Proof.
  induction ys; intros; destruct H; [auto|].
  destruct ys; [destruct H0; omega|].
  refine (IHys _ ws _); clear IHys.
  destruct H0.
  split; [omega|auto].
Qed.

Lemma qs1_inj : forall xs ys, quicksort1 xs ys -> quicksort1 xs ys \/ quicksort2 xs ys.
Proof.
  auto.
Qed.

Lemma qs2_inj : forall xs ys, quicksort2 xs ys -> quicksort1 xs ys \/ quicksort2 xs ys.
Proof.
  auto.
Qed.

Lemma qs1_split : forall n xs, Permutation xs (filter (lt_n n) xs ++ filter (ge_n n) xs).
Proof.
  intros.
  apply filter_split.
  apply Nat.ltb_antisym.
Qed.

Lemma qs2_split : forall n xs, Permutation xs (filter (le_n n) xs ++ filter (gt_n n) xs).
Proof.
  intros.
  apply filter_split.
  apply Nat.leb_antisym.
Qed.

Lemma qs_perm : forall xs ys, quicksort1 xs ys \/ quicksort2 xs ys -> Permutation xs ys.
Proof.
  intro; remember (length xs) as k.
  assert (length xs <= k) by omega; clear Heqk.
  revert xs H.
  induction k; intros.
  - apply len_0_nil in H; subst xs.
    destruct H0; inversion_clear H; auto.
  - destruct xs; [destruct H0; inversion_clear H0; auto|].
    simpl in H; assert (length xs <= k) by omega; clear H.
    destruct H0; inversion_clear H.
    all: refine (Permutation_trans _ (Permutation_middle _ _ _)).
    all: apply perm_skip.
    1: refine (Permutation_trans (qs1_split n xs) _).
    2: refine (Permutation_trans (qs2_split n xs) _).
    all: refine (Permutation_app _ _).
    all: apply IHk; [apply filter_short|]; auto.
Qed.

Lemma qs1_perm : forall xs ys, quicksort1 xs ys -> Permutation xs ys.
Proof.
  intros; apply qs_perm; auto.
Qed.

Lemma qs2_perm : forall xs ys, quicksort2 xs ys -> Permutation xs ys.
Proof.
  intros; apply qs_perm; auto.
Qed.

Lemma qs_sorted : forall xs ys, quicksort1 xs ys \/ quicksort2 xs ys -> sorted ys.
Proof.
  intro.
  remember (length xs) as k.
  assert (length xs <= k) by omega; clear Heqk.
  revert xs H.
  induction k; intros.
  - apply len_0_nil in H; subst xs.
    destruct H0; inversion_clear H; simpl; auto.
  - destruct xs; [destruct H0; inversion_clear H0; simpl; auto|].
    simpl in H; assert (length xs <= k) by omega; clear H.
    destruct H0; inversion_clear H; apply sorted_app.
    all: try clear l H0; try clear r H2.
    all: try rename l into zs; try rename H0 into H.
    all: try rename r into zs; try rename H2 into H.
    1,2: apply qs1_perm in H.
    5,6: apply qs2_perm in H.
    1,5: apply (perm_upper n) in H; [auto|].
    3,6: apply (perm_lower n) in H; [auto|].
    1-4: apply boundary.
    all: try apply qs1_inj in H; try apply qs2_inj in H.
    all: apply IHk in H; [auto|].
    all: apply filter_short; auto.
Qed.

Lemma low_head : forall x xs, sorted (x :: xs) -> lower_bound x (x :: xs).
Proof.
  unfold lower_bound; unfold all.
  induction xs; simpl; [auto|].
  intro H; destruct H.
  split; [auto|split;[auto|]].
  apply IHxs; clear IHxs.
  destruct xs; simpl; [auto|].
  split; [omega|destruct H0; auto].
Qed.

Lemma sort_uniq : forall xs ys, Permutation xs ys -> sorted xs -> sorted ys -> xs = ys.
Proof.
  induction xs; simpl; intros; [apply Permutation_nil in H; auto|].
  destruct (perm_dig a _ _ H); destruct H2.
  subst ys.
  destruct x.
  - simpl in H; apply Permutation_cons_inv in H.
    apply sorted_tail in H0.
    apply sorted_tail in H1.
    simpl; f_equal.
    apply IHxs; auto.
  - assert (a <= n).
    * specialize (low_head _ _ H0); intro.
      destruct (perm_lower _ _ H2 _ H); auto.
    * rewrite <- app_comm_cons in H1.
      assert (n <= a) by (apply sort_mid in H1; auto).
      assert (n = a) by omega; clear H2 H3.
      subst n; simpl; f_equal.
      apply sorted_tail in H0.
      apply sorted_tail in H1.
      simpl in H; apply Permutation_cons_inv in H.
      apply IHxs; auto.
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
  - apply (qs_sorted x); auto.
  - apply (qs_sorted x); auto.
Qed.
