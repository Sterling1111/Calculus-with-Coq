From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_24_a : forall g : R -> R, 
  (forall x y, x <> y -> g x <> g y) -> exists f : R -> R, f ∘ g = (fun x => x).
Proof.
Admitted.

Lemma lemma_3_24_b : forall f : R -> R, 
  (forall b, exists a, b = f a) -> exists g : R -> R, f ∘ g = (fun x => x).
Proof.
Admitted.
