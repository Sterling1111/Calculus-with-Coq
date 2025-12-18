From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_6_i : ∀ f g f' g' a,
  f = (λ x, g (x + g a)) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> f' = (λ x, g' (x + g a)).
Proof.
  intros f g f' g' a H1 H2 H3.
  assert (H4 : ⟦ der ⟧ (λ x : ℝ, g (x + g a)) = (λ x : ℝ, g' (x + g a))) by auto_diff.
  rewrite (derivative_of_function_unique f f' (λ x : ℝ, g' (x + g a)) H2 ltac:(subst; auto)). reflexivity.
Qed.

Lemma lemma_10_6_ii : ∀ f g f' g' a,
  f = (λ x, g (x * g a)) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> f' = (λ x, g' (x * g a) * g a).
Proof. 
  intros f g f' g' a H1 H2 H3.
  assert (H4 : ⟦ der ⟧ (λ x : ℝ, g (x * g a)) = (λ x : ℝ, g' (x * g a) * g a)) by auto_diff.
  rewrite (derivative_of_function_unique f f' (λ x : ℝ, g' (x * g a) * g a) H2 ltac:(subst; auto)). reflexivity.
Qed.

Lemma lemma_10_6_iii : ∀ f g f' g',
  f = (λ x, g (x + g x)) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> f' = (λ x, g' (x + g x) * (1 + g' x)).
Proof.
  intros f g f' g' H1 H2 H3.
  assert (H4 : ⟦ der ⟧ (λ x : ℝ, g (x + g x)) = (λ x : ℝ, g' (x + g x) * (1 + g' x))) by auto_diff.
  rewrite (derivative_of_function_unique f f' (λ x : ℝ, g' (x + g x) * (1 + g' x)) H2 ltac:(subst; auto)). reflexivity.
Qed.

Lemma lemma_10_6_iv : ∀ f g f' g' a,
  f = (λ x, g x * (x - a)) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> f' = (λ x, g' x * (x - a) + g x).
Proof.
  intros f g f' g' a H1 H2 H3.
  assert (H4 : ⟦ der ⟧ (λ x : ℝ, g x * (x - a)) = (λ x : ℝ, g' x * (x - a) + g x)) by auto_diff.
  rewrite (derivative_of_function_unique f f' (λ x : ℝ, g' x * (x - a) + g x) H2 ltac:(subst; auto)). reflexivity.
Qed.

Lemma lemma_10_6_v : ∀ f g f' a,
  f = (λ x, g a * (x - a)) -> ⟦ der ⟧ f = f' -> f' = (λ x, g a).
Proof.
  intros f g f' a H1 H2.
  assert (H3 : ⟦ der ⟧ (λ x : ℝ, g a * (x - a)) = (λ x : ℝ, g a)) by auto_diff.
  rewrite (derivative_of_function_unique f f' (λ x : ℝ, g a) H2 ltac:(subst; auto)). reflexivity.
Qed.

Lemma lemma_10_6_vi : ∀ f g f' g',
  f = (λ x, g ((x - 3)^2)) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> f' = (λ x, g' ((x - 3)^2) * (2 * (x - 3))).
Proof.
  intros f g f' g' H1 H2 H3.
  assert (H4 : ⟦ der ⟧ (λ x : ℝ, g ((x - 3)^2)) = (λ x : ℝ, g' ((x - 3)^2) * (2 * (x - 3)))) by auto_diff.
  rewrite (derivative_of_function_unique f f' (λ x : ℝ, g' ((x - 3)^2) * (2 * (x - 3)) ) H2 ltac:(subst; auto)). reflexivity.
Qed.
