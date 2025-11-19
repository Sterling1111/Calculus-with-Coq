From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_18 : ∀ f a l,
  ⟦ lim a ⟧ f = l →
  ∃ δ M, δ > 0 /\ (∀ x, 0 < |x - a| < δ → |f x| < M).
Proof.
Admitted.