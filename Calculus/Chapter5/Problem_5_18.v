From Calculus.Chapter5 Require Import Prelude.
Open Scope R_scope.

Lemma lemma_5_18 : ∀ (f : R → R) (a l : R),
  ⟦ lim a ⟧ f = l →
  ∃ δ M, δ > 0 /\ M > 0 /\ (∀ x, 0 < |x - a| < δ → |f x| < M).
Proof. Admitted.
