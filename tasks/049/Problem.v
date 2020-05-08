(*
                       j
   -------------------->
  | 0  1  3  6  10  ...
  |    2  4  7  11  ...
  |       5  8  12  ...
  |          9  13  ...
  |             14  ...
  |
i V

*)

Inductive visit : nat -> nat -> Prop :=
| visit_first : visit 0 0
| visit_down : forall i j, i < j -> visit i j -> visit (S i) j
| visit_right : forall i j, i >= j -> visit i j -> visit 0 (S j).

Definition task := forall i j, i <= j -> visit i j.
