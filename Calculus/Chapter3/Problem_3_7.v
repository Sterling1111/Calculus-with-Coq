From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_7_a : forall (l : list R) (a : R), 
  exists (g : list R) (b : R), forall x, polynomial l x = (x - a) * polynomial g x + b.
Proof.
Admitted.

Lemma lemma_3_7_b : forall (l : list R) (a : R), 
  polynomial l a = 0 -> exists (g : list R), forall x, polynomial l x = (x - a) * polynomial g x.
Proof.
Admitted.
