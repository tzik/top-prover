Require Import Problem.

(* Hint *)
Lemma lemma: forall (f: bool -> bool) b x y z,
    x = f b -> y = f x -> z = f y -> z = x.
Proof.
  (* FILL IN HERE *)
Qed.

Theorem solution: task.
Proof. unfold task. intros. eapply lemma; reflexivity. Qed.
