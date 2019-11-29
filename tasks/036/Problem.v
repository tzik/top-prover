Require Import ZArith Znumtheory.
Open Scope Z.

Definition Square (n : Z) := Z.sqrt n * Z.sqrt n = n.

Definition task := forall n m, 1 <= n -> 1 <= m -> rel_prime n m -> Square (n * m) -> Square n.