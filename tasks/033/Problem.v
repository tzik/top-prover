Inductive T := Leaf : T | Node : T -> T -> T.

Definition task := forall x y z w, Node x y = Node z w -> x = z /\ y = w.
