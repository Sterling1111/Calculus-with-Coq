From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_22_if : ∀ (f : R → R) (L : R),
  ⟦ lim 0 ⟧ f = L → 
  (∀ g, (~ ∃ L1, ⟦ lim 0 ⟧ g = L1) → (~ ∃ L2, ⟦ lim 0 ⟧ (fun x => f x + g x) = L2)).
Proof. Admitted.

Lemma lemma_5_22_only_if : ∀ (f : R → R),
  (∀ g, (~ ∃ L1, ⟦ lim 0 ⟧ g = L1) → (~ ∃ L2, ⟦ lim 0 ⟧ (fun x => f x + g x) = L2)) → 
  ∃ L, ⟦ lim 0 ⟧ f = L.
Proof. Admitted.
