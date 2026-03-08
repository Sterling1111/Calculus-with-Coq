From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_4_i : ∀ f f', f = (λ x, 1 / (1 + x)) -> ⟦ der ⟧ f = f' -> ∀ x, x <> -1 -> f' (f x) = - (1 + x)^2 / (2 + x)^2.
Proof. Admitted.

Lemma lemma_10_4_ii : ∀ f f', f = (λ x, sin x) -> ⟦ der ⟧ f = f' -> ∀ x, f' (f x) = cos (sin x).
Proof. Admitted.

Lemma lemma_10_4_iii : ∀ f f', f = (λ x, x^2) -> ⟦ der ⟧ f = f' -> ∀ x, f' (f x) = 2 * x^2.
Proof. Admitted.

Lemma lemma_10_4_iv : ∀ f f', f = (λ x, 17) -> ⟦ der ⟧ f = f' -> ∀ x, f' (f x) = 0.
Proof. Admitted.
