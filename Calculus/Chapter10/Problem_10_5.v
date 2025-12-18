From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_5_i : ∀ f f' x,
  f = (λ x, 1 / x) -> x ≠ 0 -> ⟦ der x ⟧ f = f' -> f (f'(x)) = -x^2.
Proof.
  intros f f' x H1 H2 H3.
  assert (H4 : ⟦ der x ⟧ f = (λ x, -1 / x^2)).
  {
    set (fn := λ x : ℝ, 1). set (fd := λ x : ℝ, x). set (fn' := λ x : ℝ, 0). set (fd' := λ x : ℝ, 1).
    assert (H5 : ⟦ der x ⟧ fn = fn') by apply theorem_10_1.
    assert (H6 : ⟦ der x ⟧ fd = fd') by apply theorem_10_2.
    pose proof theorem_10_8 fn fn' fd fd' x H5 H6 ltac:(auto) as H7.
    replace (fn / fd)%f with f in H7. unfold derivative_at in H7. unfold derivative_at.
    replace ((fd x * fn' x - fn x * fd' x) / (fd x * fd x)) with (-1 / x ^ 2) in H7.
    2 : { unfold fn, fd, fn', fd'. field; auto. } auto.
  }
  rewrite (derivative_of_function_at_x_unique f f' (λ x : ℝ, -1 / x ^ 2) x H3 H4), H1. field; auto.
Qed.

Lemma lemma_10_5_ii : ∀ f f',
  f = (λ x, x^2) -> ⟦ der ⟧ f = f' -> ∀ x, f (f'(x)) = 4 * x^2.
Proof.
  intros f f' H1 H2 x.
  assert (H3 : ⟦ der ⟧ f = (λ x, 2 * x)).
  {
    rewrite H1. replace (λ x0 : ℝ, 2 * x0) with (λ x0 : ℝ, 2 * x0 ^ (2 - 1)).
    2 : { extensionality y. simpl. lra. } apply power_rule'; auto. 
  }
  rewrite (derivative_of_function_unique f f' (λ x, 2 * x) H2 H3), H1. field; auto.
Qed.

Lemma lemma_10_5_iii : ∀ f f',
  f = (λ x, 17) -> ⟦ der ⟧ f = f' -> ∀ x, f (f'(x)) = 17.
Proof.
  intros f f' H1 H2 x.
  assert (H3 : ⟦ der ⟧ f = (λ _ : ℝ, 0)).
  { rewrite H1. apply theorem_10_1. }
  rewrite (derivative_of_function_unique f f' (λ _ : ℝ, 0) H2 H3), H1. simpl. lra.
Qed.

Lemma lemma_10_5_iv : ∀ f f',
  f = (λ x, 17 * x) -> ⟦ der ⟧ f = f' -> ∀ x, f (f'(x)) = 289.
Proof.
  intros f f' H1 H2 x.
  assert (H3 : ⟦ der ⟧ f = (λ _ : ℝ, 17)).
  {
    rewrite H1.
    replace (λ _ : ℝ, 17) with (λ x : ℝ, 17 * 1).
    2 : { extensionality y. lra. }
    apply theorem_10_5' with (f := (λ x, x)) (f' := (λ _ : ℝ, 1)) (c := 17). apply theorem_10_2.
  }
  rewrite (derivative_of_function_unique f f' (λ _ : ℝ, 17) H2 H3), H1. field; auto.
Qed.