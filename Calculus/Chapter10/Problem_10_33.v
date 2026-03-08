From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_33_a : ∀ (n : nat) f,
  (∀ x, x ≠ 0 -> f x = x^(2 * n) * sin (1 / x)) ->
  f 0 = 0 ->
  ∀ k, (k <= n)%nat -> nth_differentiable_at k f 0.
Proof. Admitted.

Lemma lemma_10_33_b : ∀ (n : nat) f fn,
  (∀ x, x ≠ 0 -> f x = x^(2 * n) * sin (1 / x)) ->
  f 0 = 0 ->
  ⟦ der ^ n ⟧ f = fn ->
  ~ continuous_at fn 0.
Proof. Admitted.
