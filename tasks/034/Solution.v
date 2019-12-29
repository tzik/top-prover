Require Import Problem List.

Theorem solution : task.
Proof.
  unfold task.
  intro.
  induction t; simpl; intros.
  - specialize (H nil).
    destruct t'; [auto|discriminate].
  - destruct t'; [specialize (H nil); inversion H|].
    rewrite (IHt1 t'1).
    rewrite (IHt2 t'2).
    all: clear IHt1 IHt2.
    * specialize (H nil); simpl in H.
      inversion_clear H; auto.
    * intro.
      specialize (H (true :: i)).
      simpl in H; auto.
    * intro.
      specialize (H (false :: i)).
      simpl in H; auto.
Qed.
