From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_18_a : ∀ f g f' g',
  (∀ x, g x = (f x)^2) ->
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ g = g' ->
  g' = (λ x, 2 * f x * f' x).
Proof. Admitted.

Lemma lemma_10_18_b : ∀ f g f' f'' g',
  (∀ x, g x = (f' x)^2) ->
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ f' = f'' ->
  ⟦ der ⟧ g = g' ->
  g' = (λ x, 2 * f' x * f'' x).
Proof. Admitted.

Lemma lemma_10_18_c : ∀ f,
  (∀ x, f x > 0) ->
  (∀ x, (⟦ Der x ⟧ f)^2 = f x + 1 / (f x)^3) ->
  ∀ x, ⟦ Der x ⟧ (⟦ Der ⟧ f) = 1 / 2 - 3 / 2 * (1 / (f x)^4).
Proof.
Admitted.
