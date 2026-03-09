From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_25 : 
  exists f g : R -> R, g ∘ f = (fun x => x) /\ ~ exists h : R -> R, f ∘ h = (fun x => x).
Proof.
Admitted.
