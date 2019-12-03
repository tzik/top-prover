Require Import Problem List.

Theorem solution: task.
Proof.
  unfold task.
  destruct l.
  - discriminate.
  - rewrite <- app_comm_cons.
    discriminate.
Qed.
