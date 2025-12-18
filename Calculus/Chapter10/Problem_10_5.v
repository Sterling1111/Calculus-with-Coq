From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_5_i : ∀ f f' x,
  f = (λ x, 1 / x) -> x ≠ 0 -> ⟦ der x ⟧ f = f' -> f (f'(x)) = -x^2.
Proof.
  intros f f' x H1 H2 H3.
  assert (H4 : ⟦ der x ⟧ f = (λ x, -1 / x^2)) by (subst; auto_diff).
  rewrite (derivative_of_function_at_x_unique f f' (λ x : ℝ, -1 / x ^ 2) x H3 H4), H1. field; auto.
Qed.

Lemma lemma_10_5_ii : ∀ f f',
  f = (λ x, x^2) -> ⟦ der ⟧ f = f' -> ∀ x, f (f'(x)) = 4 * x^2.
Proof.
  intros f f' H1 H2 x.
  assert (H3 : ⟦ der ⟧ f = (λ x, 2 * x)) by (subst; auto_diff).
  rewrite (derivative_of_function_unique f f' (λ x, 2 * x) H2 H3), H1. field; auto.
Qed.

Lemma lemma_10_5_iii : ∀ f f',
  f = (λ x, 17) -> ⟦ der ⟧ f = f' -> ∀ x, f (f'(x)) = 17.
Proof.
  intros f f' H1 H2 x.
  assert (H3 : ⟦ der ⟧ f = (λ _ : ℝ, 0)) by (subst; auto_diff).
  rewrite (derivative_of_function_unique f f' (λ _ : ℝ, 0) H2 H3), H1. simpl. lra.
Qed.

Lemma lemma_10_5_iv : ∀ f f',
  f = (λ x, 17 * x) -> ⟦ der ⟧ f = f' -> ∀ x, f (f'(x)) = 289.
Proof.
  intros f f' H1 H2 x.
  assert (H3 : ⟦ der ⟧ f = (λ _ : ℝ, 17)) by (subst; auto_diff).
  rewrite (derivative_of_function_unique f f' (λ _ : ℝ, 17) H2 H3), H1. field; auto.
Qed.