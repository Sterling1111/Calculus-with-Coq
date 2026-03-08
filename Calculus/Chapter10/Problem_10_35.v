From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_35_i : ∀ f g, f = (λ y, sin y) -> g = (λ x, x + x^2) ->
  ⟦ der ⟧ (f ∘ g) = (λ x, cos (x + x^2) * (1 + 2 * x)).
Proof. Admitted.

Lemma lemma_10_35_ii : ∀ f g, f = (λ y, sin y) -> g = (λ x, cos x) ->
  ⟦ der ⟧ (f ∘ g) = (λ x, cos (cos x) * (- sin x)).
Proof. Admitted.

Lemma lemma_10_35_iii : ∀ f g, f = (λ u, sin u) -> g = (λ x, sin x) ->
  ⟦ der ⟧ (f ∘ g) = (λ x, cos (sin x) * cos x).
Proof. Admitted.

Lemma lemma_10_35_iv : ∀ f g h, f = (λ v, sin v) -> g = (λ u, cos u) -> h = (λ x, sin x) ->
  ⟦ der ⟧ (f ∘ g ∘ h) = (λ x, cos (cos (sin x)) * (- sin (sin x) * cos x)).
Proof. Admitted.
