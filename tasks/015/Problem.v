Require Import Sorting.Permutation.

Definition task :=
  forall a b (l : list nat),
    Permutation (a :: l) (b :: l) -> a = b.
