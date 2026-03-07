From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_31 : ∀ (f : R -> R) a L1 L2,
  ⟦ lim a⁻ ⟧ f = L1 -> ⟦ lim a⁺ ⟧ f = L2 -> L1 < L2 ->
  ∃ δ, δ > 0 /\ ∀ x y, x < a -> a < y -> |x - a| < δ -> |y - a| < δ -> f x < f y.
Proof. Admitted.
