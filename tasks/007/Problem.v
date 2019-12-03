Fixpoint product_of_range from count :=
  match count with
  | O => 1
  | S count' => (S from) * product_of_range (S from) count'
  end.

Definition task :=
  forall from count, exists k,
      product_of_range from count = k * product_of_range O count.
