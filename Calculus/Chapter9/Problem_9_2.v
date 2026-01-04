From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_2_a : ∀ a f f',
  a <> 0 -> f = (λ x, 1 / x^2) -> ⟦ der a ⟧ f = f' -> f' a = -2 / (a ^ 3).
Proof.
  intros a f f' H1 H2 H3.
  assert (H4 : ⟦ der a ⟧ f = (λ x, -2 / (x ^ 3))).
  {
    rewrite H2. unfold derivative_at.
    apply limit_eq with (f1 := (λ h, ((-2 * a - h) / (a^2 * (a + h)^2))) ).
    - exists (|a/2|). split; [| intros h H5 ]; solve_R.
    - auto_limit; rewrite Rplus_0_r, Rmult_1_r; repeat apply Rmult_integral_contrapositive; auto.
  }
  rewrite (derivative_at_unique f f' (λ x, -2 / (x ^ 3)) a H3 H4); auto.
Qed.

Lemma lemma_9_2_b : ∀ (a : R) (f f' : R -> R),
  let g := tangent_line f f' a in
  a <> 0 ->
  f = (λ x, 1 / x^2) ->
  ⟦ der a ⟧ f = f' ->
  ∀ x, x <> 0 -> f x = g x -> x = a \/ x = -a/2.
Proof.
  intros a f f' g H1 H2 H3 x H4 H5.
  pose proof (lemma_9_2_a a f f' H1 H2 H3) as H6.
  subst. unfold g, tangent_line in H5. rewrite H6 in H5. 
  apply Rmult_eq_compat_r with (r := x^2 * a^3),
  Rminus_eq_compat_r with (r := -2 * x ^ 3 + 3 * x ^ 2 * a) in H5; field_simplify in H5; auto.
  replace (2 * x ^ 3 - 3 * x ^ 2 * a + a ^ 3) with ((x - a) * (2 * x + a)) in H5 by nra.
  apply Rmult_integral in H5 as [H5 | H5]; lra.
Qed.