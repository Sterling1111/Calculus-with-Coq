From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_23_a : forall f g : R -> R, 
  f ∘ g = (fun x => x) -> forall x y, x <> y -> g x <> g y.
Proof.
Admitted.

Lemma lemma_3_23_b : forall f g : R -> R, 
  f ∘ g = (fun x => x) -> forall b, exists a, b = f a.
Proof.
Admitted.
