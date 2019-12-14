Require Import Problem List Omega.

Lemma decomp (xs : list nat) : xs = nil \/ (exists ys zs, xs = ys ++ (0 :: nil) ++ zs) \/ (exists ys, xs = map S ys).
Proof.
  induction xs; [auto|].
  destruct IHxs.
  - subst xs.
    right.
    destruct a.
    * left; exists nil; exists nil; auto.
    * right; exists (a :: nil); simpl; auto.
  - right.
    destruct a.
    * left; exists nil; exists xs; simpl; auto.
    * destruct H.
      + destruct H; destruct H.
        left; exists (S a :: x); exists x0.
        rewrite H.
        auto.
      + right.
        destruct H.
        subst xs.
        exists (a :: x).
        simpl; auto.
Qed.

Definition maximum := fold_right max 0.

Lemma c2_app : forall xs ys, compute2 (xs ++ (0 :: nil) ++ ys) = compute2 xs + compute2 ys.
Proof.
  induction xs.
  - simpl.
    destruct ys; simpl; auto.
  - destruct xs.
    * simpl.
      rewrite Nat.min_0_r.
      destruct ys; simpl; omega.
    * intros.
      rewrite <- app_comm_cons.
      rewrite <- app_comm_cons.
      assert (forall x y zs, compute2 (x :: y :: zs) = x - min x y + compute2 (y :: zs)) by (simpl; auto).
      repeat rewrite H.
      rewrite app_comm_cons.
      rewrite IHxs.
      omega.
Qed.

Lemma length_hom : forall xs ys : list nat, length (xs ++ ys) = length xs + length ys.
Proof.
  induction xs; simpl; [auto|].
  intros.
  rewrite IHxs.
  auto.
Qed.

Lemma maximum_hom : forall xs ys : list nat, maximum (xs ++ ys) = max (maximum xs) (maximum ys).
Proof.
  induction xs; simpl; [auto|].
  intro.
  rewrite IHxs.
  rewrite Nat.max_assoc.
  auto.
Qed.

Lemma c2_succ : forall x xs, compute2 (map S (x :: xs)) = S (compute2 (x :: xs)).
Proof.
  intros; generalize x; clear x.
  induction xs; [simpl; auto|].
  intros.
  specialize (IHxs a).
  assert (forall y z ws, compute2 (y :: z :: ws) = compute2 (z :: ws) + (y - min y z)) by (intros; simpl; omega).
  rewrite H.
  rewrite <- Nat.add_succ_l.
  rewrite <- IHxs.
  simpl; omega.
Qed.

Lemma map_S : forall xs, map S xs = map (fun x => S x) xs.
Proof.
  induction xs; simpl; [auto|].
  rewrite IHxs; auto.
Qed.

Lemma length_map : forall xs, length (map S xs) = length xs.
Proof.
  induction xs; simpl; [|rewrite IHxs]; auto.
Qed.

Lemma maximum_S : forall x xs, maximum (map S (x :: xs)) = S (maximum (x :: xs)).
Proof.
  intros; revert x.
  induction xs; intros.
  - simpl.
    rewrite Nat.max_0_r.
    auto.
  - replace (S (maximum (x :: a :: xs))) with (max (S x) (S (maximum (a :: xs)))) by (simpl; auto).
    rewrite <- IHxs.
    simpl; auto.
Qed.

Theorem solution: task.
Proof.
  unfold task.
  intros.

  remember (length l + maximum l) as k.
  apply eq_sym in Heqk; apply Nat.eq_le_incl in Heqk.
  revert l Heqk.

  induction k; intros.
  - assert (length l = 0) by omega; clear Heqk.
    destruct l.
    * simpl; constructor.
    * simpl in H; discriminate.
  - destruct (decomp l).
    * subst l; simpl; constructor.
    * destruct H.
      + destruct H; destruct H.
        subst l.
        rewrite c2_app.
        repeat rewrite length_hom in Heqk.
        repeat rewrite maximum_hom in Heqk.
        simpl in Heqk.
        apply c1_app; apply IHk.
        -- specialize (Nat.le_max_l (maximum x) (maximum x0)); omega.
        -- specialize (Nat.le_max_r (maximum x) (maximum x0)); omega.
      + destruct H; subst l.
        destruct x.
        simpl; constructor.
        rewrite c2_succ.
        rewrite map_S.
        apply c1_succ.
        apply IHk.
        rewrite length_map in Heqk.
        rewrite maximum_S in Heqk.
        omega.
Qed.
