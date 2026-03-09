From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_27_c : forall f : R -> R, 
  (forall g : R -> R, f ∘ g = g ∘ f) -> forall x, f x = x.
Proof.
Admitted.
