From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_1_a : ∀ a f f',
  a <> 0 -> f = (λ x, 1 / x) -> ⟦ der a ⟧ f = f' -> f' a = -1 / (a ^ 2).
Proof.
  intros a f f' H1 H2 H3.
  assert (H4 : ⟦ der a ⟧ f = (λ x, -1 / (x ^ 2))).
  {
    rewrite H2. unfold derivative_at. 
    apply limit_eq with (f1 := (λ h : ℝ, -1 / ((a + h) * a))).
    - exists (|a/2|). split; [| intros h H5 ]; solve_R.
    - auto_limit.
  }
  rewrite (derivative_at_unique f f' (λ x, -1 / (x ^ 2)) a H3 H4); auto.
Qed.

Lemma lemma_9_1_a' : ∀ a f f',
  a <> 0 -> f = (λ x, 1 / x) -> ⟦ der a ⟧ f = f' -> f' a = -1 / (a ^ 2).
Proof.
  intros a f f' H1 H2 H3. 
  assert (H4 : ⟦ der a ⟧ f = (λ x, -1 / (x ^ 2))) by (subst; auto_diff).
  rewrite (derivative_at_unique f f' (λ x, -1 / (x ^ 2)) a H3 H4); auto.
Qed.

Lemma lemma_9_1_b : ∀ (a : R) (f f' : R -> R),
  let g := tangent_line f f' a in
  a ≠ 0 ->
  f = (fun x => 1 / x) ->
  ⟦ der a ⟧ f = f' ->
  ∀ x, x <> 0 -> f x = g x -> x = a.
Proof.
  intros a f f' g H1 H2 H3 x H4 H5.
  pose proof (lemma_9_1_a a f f' H1 H2 H3) as H6.
  subst. unfold g, tangent_line in H5. rewrite H6 in H5. apply Rmult_eq_compat_r with (r := x * a^2),
  Rminus_eq_compat_r with (r := -x^2 + 2 * x * a) in H5; field_simplify in H5; auto.
  replace (x ^ 2 - 2 * x * a + a ^ 2) with ((x - a) * (x - a)) in H5 by lra.
  apply Rmult_integral in H5 as [H5 | H5]; lra.
Qed.