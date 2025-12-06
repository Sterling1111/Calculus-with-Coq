From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_1_i : ⟦ der ⟧ (λ x, sin (x + x^2)) = (λ x, cos (x + x^2) * (1 + 2 * x)).
Proof.
  set (f := λ x, sin x).
  set (f' := λ x, cos x).
  set (g := λ x, x + x^2).
  set (g' := λ x, 1 + 2 * x).

  replace (λ x, f (x + x^2)) with (f ∘ g) by reflexivity.
  replace (λ x : ℝ, f' (x + x ^ 2) * (1 + 2 * x)) with ((f' ∘ g) ∙ g') by reflexivity.
  
  assert (H1 : ⟦ der ⟧ f = f') by apply sin_derivative.
  assert (H2 : ⟦ der ⟧ g = g').
  { unfold g. apply theorem_10_3_b. apply theorem_10_2. admit. }
  apply chain_rule; auto.
Admitted.