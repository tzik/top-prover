Require Import List.

Fixpoint prefix_sum sum l :=
  match l with
  | nil => sum :: nil
  | head :: tail => sum :: prefix_sum (sum + head) tail
  end.

Fixpoint plus_list l1 l2 :=
  match (l1, l2) with
  | (nil, _) => nil
  | (_, nil) => nil
  | (h1 :: t1, h2 :: t2) => (h1 + h2) :: plus_list t1 t2
  end.

Definition task :=
  forall l1 l2,
    prefix_sum 0 (plus_list l1 l2) =
    plus_list (prefix_sum 0 l1) (prefix_sum 0 l2).
