From Calculus.Chapter10 Require Import Prelude.

Definition Schwarzian_derivative (f : ℝ -> ℝ) (x : ℝ) : ℝ :=
  ⟦ Der x ⟧ (⟦ Der ⟧ (⟦ Der ⟧ f)) / ⟦ Der x ⟧ f - 3 / 2 * (⟦ Der x ⟧ (⟦ Der ⟧ f) / ⟦ Der x ⟧ f)^2.

Lemma lemma_10_19_a : ∀ f g x,
  Schwarzian_derivative (f ∘ g) x = Schwarzian_derivative f (g x) * (⟦ Der x ⟧ g)^2 + Schwarzian_derivative g x.
Proof. Admitted.

Lemma lemma_10_19_b : ∀ a b c d,
  a * d - b * c ≠ 0 ->
  ∀ x, c * x + d ≠ 0 ->
  Schwarzian_derivative (λ x, (a * x + b) / (c * x + d)) x = 0.
Proof. Admitted.
