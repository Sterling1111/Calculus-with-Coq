From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_28_a : forall a b M f f',
  a < b ->
  ⟦ der ⟧ f = f' ->
  (forall x, x ∈ [a, b] -> f' x >= M) ->
  f b >= f a + M * (b - a).
Proof.
  intros a b M f f' H1 H2 H3.
  assert (H4 : continuous_on f [a, b]).
  {
    apply continuous_imp_continuous_on, differentiable_imp_continuous,
    (derivative_imp_differentiable f f'); auto.
  }
  assert (H5 : ⟦ der ⟧ f (a, b) = f').
  { apply derivative_imp_derivative_on; auto. apply differentiable_domain_open; auto. }
  pose proof MVT f f' a b H1 H4 H5 as [x [H6 H7]].
  specialize (H3 x ltac:(solve_R)).
  apply Rmult_eq_compat_r with (r := b - a) in H7.
  field_simplify in H7; nra.
Qed.

Lemma lemma_11_28_b : forall a b M f f',
  a < b ->
  ⟦ der ⟧ f = f' ->
  (forall x, x ∈ [a, b] -> f' x <= M) ->
  f b <= f a + M * (b - a).
Proof.
  intros a b M f f' H1 H2 H3.
  assert (H4 : continuous_on f [a, b]).
  {
    apply continuous_imp_continuous_on, differentiable_imp_continuous,
    (derivative_imp_differentiable f f'); auto.
  }
  assert (H5 : ⟦ der ⟧ f (a, b) = f').
  { apply derivative_imp_derivative_on; auto. apply differentiable_domain_open; auto. }
  pose proof MVT f f' a b H1 H4 H5 as [x [H6 H7]].
  specialize (H3 x ltac:(solve_R)).
  apply Rmult_eq_compat_r with (r := b - a) in H7.
  field_simplify in H7; nra.
Qed.

Lemma lemma_11_28_c : forall a b M f f',
  a < b ->
  ⟦ der ⟧ f = f' ->
  (forall x, x ∈ [a, b] -> |f' x| <= M) ->
  |f b - f a| <= M * (b - a).
Proof.
  intros a b M f f' H1 H2 H3.
  assert (H4 : forall x, x ∈ [a, b] -> f' x >= -M).
  { intros x H4. specialize (H3 x H4). solve_R. }
  assert (H5 : forall x, x ∈ [a, b] -> f' x <= M).
  { intros x H5. specialize (H3 x H5). solve_R. }
  pose proof lemma_11_28_a a b (-M) f f' H1 H2 H4 as H6.
  pose proof lemma_11_28_b a b M f f' H1 H2 H5 as H7.
  solve_R.
Qed.