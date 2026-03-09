From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_15_a : forall f : R -> R, 
  forall x, f x = Rmax (f x) 0 + Rmin (f x) 0.
Proof.
Admitted.

Lemma lemma_3_15_b : forall f : R -> R, 
  exists g h : R -> R, (forall x, g x >= 0) /\ (forall x, h x >= 0) /\ forall x, f x = g x - h x.
Proof.
Admitted.
