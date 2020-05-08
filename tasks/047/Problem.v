Definition task :=
  forall P : bool -> bool, exists a, P a = true -> forall x, P x = true.
