From Calculus.Chapter5 Require Import Prelude.
Open Scope R_scope.

Lemma lemma_5_29 : ∀ (f : R → R) (a L : R),
  ⟦ lim a⁺ ⟧ f = L →
  ⟦ lim a⁻ ⟧ f = L →
  ⟦ lim a ⟧ f = L.
Proof. Admitted.
