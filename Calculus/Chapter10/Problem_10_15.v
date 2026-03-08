From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_15_a : ~ (∀ f g a, differentiable_at (λ x, f x + g x) a -> differentiable_at f a /\ differentiable_at g a).
Proof. Admitted.

Lemma lemma_10_15_b : ∀ f g a,
  differentiable_at f a ->
  f a ≠ 0 ->
  differentiable_at (λ x, f x * g x) a ->
  differentiable_at g a.
Proof. Admitted.
