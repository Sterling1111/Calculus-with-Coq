From Lib Require Import Imports Sets Limit Continuity Derivative Notations Reals_util.
Import LimitNotations IntervalNotations SetNotations DerivativeNotations Function_Notations.
Open Scope R_scope.

Lemma lemma_10_6_i : ∀ f g f' g' a,
  f = (λ x, g (x + g a)) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> f' = (λ x, g' (x + g a)).
Proof.
  intros f g f' g' a H1 H2 H3. set (h := λ x, x + g a). set (h' := λ _ : ℝ, 1).
  replace (λ x : ℝ, g (x + g a)) with (g ∘ h) in * by (extensionality y; reflexivity).
  replace  (λ x : ℝ, g' (x + g a)) with (g' ∘ h) by (extensionality y; reflexivity).
  assert (H4 : ⟦ der ⟧ h = h').
  {
    unfold h, h'. replace (λ _ : ℝ, 1) with (λ x : ℝ, 1 + 0) by (extensionality y; apply Rplus_0_r).
    apply theorem_10_3_b; [ apply theorem_10_2 | apply theorem_10_1 ].
  }
  assert (H5 : ⟦ der ⟧ f = (g' ∘ h) ∙ h') by (rewrite H1; apply chain_rule; auto).
  replace (g' ∘ h) with (g' ∘ h ∙ h'). 2 : { unfold h'. extensionality y. apply Rmult_1_r. }
  rewrite (derivative_of_function_unique f f' (g' ∘ h ∙ h') H2 H5). reflexivity.
Qed.

Lemma lemma_10_6_ii : ∀ f g f' g' a,
  f = (λ x, g (x * g a)) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> f' = (λ x, g' (x * g a) * g a).
Proof. Admitted.

Lemma lemma_10_6_iii : ∀ f g f' g',
  f = (λ x, g (x + g x)) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> f' = (λ x, g' (x + g x) * (1 + g' x)).
Proof. Admitted.

Lemma lemma_10_6_iv : ∀ f g f' g' a,
  f = (λ x, g x * (x - a)) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> f' = (λ x, g' x * (x - a) + g x).
Proof. Admitted.

Lemma lemma_10_6_v : ∀ f g f' a,
  f = (λ x, g a * (x - a)) -> ⟦ der ⟧ f = f' -> f' = (λ x, g a).
Proof. Admitted.

Lemma lemma_10_6_vi : ∀ f g f' g',
  f = (λ x, g ((x - 3)^2)) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> f' = (λ x, g' ((x - 3)^2) * (2 * (x - 3))).
Proof. Admitted.
