From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_7 : ∃ (f : R -> R) (l a : R) (ε δ : R), 
  ε > 0 /\ δ > 0 /\
  (∀ x, 0 < |x - a| < δ -> |f x - l| < ε) /\
  ¬ (∀ x, 0 < |x - a| < δ/2 -> |f x - l| < ε/2).
Proof. Admitted.
