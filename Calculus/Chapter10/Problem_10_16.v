From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_16_a : ∀ f a,
  differentiable_at f a ->
  f a ≠ 0 ->
  differentiable_at (λ x, | f x |) a.
Proof. Admitted.

Lemma lemma_10_16_b : ∃ f a,
  differentiable_at f a /\ f a = 0 /\ ~ differentiable_at (λ x, | f x |) a.
Proof. Admitted.

Lemma lemma_10_16_c : ∀ f g a,
  differentiable_at f a ->
  differentiable_at g a ->
  f a ≠ g a ->
  differentiable_at (λ x, Rmax (f x) (g x)) a /\ differentiable_at (λ x, Rmin (f x) (g x)) a.
Proof. Admitted.

Lemma lemma_10_16_d : ∃ f g a,
  differentiable_at f a /\ differentiable_at g a /\ f a = g a /\
  ~ differentiable_at (λ x, Rmax (f x) (g x)) a.
Proof. Admitted.
