From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_29 : ∀ f,
  differentiable_at f 0 ->
  f 0 = 0 ->
  ∃ g, (∀ x, f x = x * g x) /\ continuous_at g 0.
Proof. Admitted.
