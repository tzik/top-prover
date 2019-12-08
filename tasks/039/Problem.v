Definition task :=
  (forall P Q R, (P <-> Q) \/ (Q <-> R) \/ (R <-> P))
  -> forall P, P \/ ~ P.
