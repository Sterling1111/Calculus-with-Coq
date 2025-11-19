From Calculus.Chapter5 Require Import Prelude.
Open Scope R_scope.

Lemma lemma_5_21_b : ∀ (g h : R → R) (M : R),
  (∀ x, |h x| <= M) →
  ⟦ lim 0 ⟧ g = 0 →
  ⟦ lim 0 ⟧ (fun x => g x * h x) = 0.
Proof. Admitted.
