From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_34 : ∀ (f : R -> R) L,
  ⟦ lim 0⁺ ⟧ (fun x => f (1 / x)) = L <-> ⟦ lim ∞ ⟧ f = L.
Proof. Admitted.
