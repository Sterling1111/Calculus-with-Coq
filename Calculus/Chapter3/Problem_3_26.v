From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_26 : forall f g h : R -> R, 
  f ∘ g = (fun x => x) -> h ∘ f = (fun x => x) -> g = h.
Proof.
Admitted.
