From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_22_a : forall f g h : R -> R, 
  g = h ∘ f -> forall x y, f x = f y -> g x = g y.
Proof.
Admitted.

Lemma lemma_3_22_b : forall f g : R -> R, 
  (forall x y, f x = f y -> g x = g y) -> exists h : R -> R, g = h ∘ f.
Proof.
Admitted.
