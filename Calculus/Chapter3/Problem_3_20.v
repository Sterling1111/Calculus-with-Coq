From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_20_a : 
  exists f : R -> R, ~(exists c, forall x, f x = c) /\ forall x y, | f y - f x | <= | y - x |.
Proof.
Admitted.

Lemma lemma_3_20_b : forall f : R -> R, 
  (forall x y, f y - f x <= (y - x)^2) -> exists c, forall x, f x = c.
Proof.
Admitted.
