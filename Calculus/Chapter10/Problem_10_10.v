From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_10 : ∀ f h k,
  (∀ x, x ≠ 0 -> f x = x^2 * sin (1 / x)) ->
  f 0 = 0 ->
  ⟦ der ⟧ h = (λ x, sin (sin (x + 1))^2) ->
  h 0 = 3 ->
  ⟦ der ⟧ k = (λ x, f (x + 1)) ->
  k 0 = 0 ->
  ∀ α, α = (λ x, h (x^2)) ->
  (⟦ Der 0 ⟧ (f ∘ h) = 0) /\ (⟦ Der 0 ⟧ (k ∘ f) = 0) /\ (⟦ Der 0 ⟧ α = 0).
Proof. Admitted.
