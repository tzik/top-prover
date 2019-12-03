Require Import List.

Definition task := forall l: list nat, app l (0 :: nil) <> nil.
