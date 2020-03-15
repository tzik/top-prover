Definition ext_eq {A B} (f g : A -> B) := forall a, f a = g a.

Definition task :=
  forall A B (f g : A -> B), ext_eq f g -> ext_eq g f.
