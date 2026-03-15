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
    - auto_limit; simpl; rewrite Rplus_0_r, Rmult_1_r; repeat apply Rmult_integral_contrapositive; auto.
  }
  rewrite (derivative_at_unique f f' (λ x, -2 / (x ^ 3)) a H3 H4); auto.
Qed.

Lemma lemma_9_2_b : ∀ (a : R) (f : R -> R),
  let g := tangent_line f a in
  a <> 0 ->
  f = (λ x, 1 / x^2) ->
  ∀ x, x <> 0 -> f x = g x -> x = a \/ x = -a/2.
Proof.
  intros a f g H1 H2 x H3 H4.
  assert (H5 : ⟦ der a ⟧ f = (λ x, -2 / x^3)).
  {
    rewrite H2. unfold derivative_at.
    apply limit_eq with (f1 := (λ h, ((-2 * a - h) / (a^2 * (a + h)^2))) ).
    - exists (|a/2|). split; [| intros h H5 ]; solve_R.
    - auto_limit; simpl; rewrite Rplus_0_r, Rmult_1_r; repeat apply Rmult_integral_contrapositive; auto.
  }
  pose proof (derivative_at_imp_derive_at f (λ x, -2 / x^3) a H5) as H6.
  subst. unfold g, tangent_line in H4. rewrite H6 in H4. 
  apply Rmult_eq_compat_r with (r := x^2 * a^3),
  Rminus_eq_compat_r with (r := -2 * x ^ 3 + 3 * x ^ 2 * a) in H4; field_simplify in H4; auto.
  replace (2 * x ^ 3 - 3 * x ^ 2 * a + a ^ 3) with ((x - a) * (x - a) * (2 * x + a)) in H4 by nra.
  apply Rmult_integral in H4 as [H4 | H4]; nra.
Qed.