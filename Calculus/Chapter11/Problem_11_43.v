From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_43 : forall f f',
  ⟦ der ⟧ f = f' ->
  (forall x, x > 0 -> f' x = 1 / x) -> f 1 = 0 ->
  forall x y, x > 0 -> y > 0 -> f (x * y) = f x + f y.
Proof.
  intros f f' H1 H2 H3 x y H4 H5.
  set (g := fun x => f (x * y)).
  assert (H6 : forall z, z > 0 -> ⟦ der z ⟧ g = f').
  {
    intros z H6.
    assert (H7 : ⟦ der ⟧ g = (fun x => y * f' (x * y))) by (unfold g; auto_diff).
    specialize (H7 z). apply derivative_at_ext' with (f1 := λ x : ℝ, y * f' (x * y)); auto.
    exists (z / 2). split; try lra. intros h H8. repeat rewrite H2; solve_R.
  }
  set (a := Rmin 1 x / 2).
  set (b := Rmax 1 x + 1).
  assert (H7 : a < b) by (unfold a, b; solve_R).
  assert (H8 : ∀ z, z ∈ [a, b] → ⟦ der z ⟧ g = f').
  { intros z H8. apply H6. unfold a, b in H8. solve_R. }
  assert (H9 : ∀ z, z ∈ [a, b] → ⟦ der z ⟧ f = f').
  { intros z H9. apply H1. }
  assert (H10 : ∀ z, z ∈ [a, b] → f' z = f' z) by auto.
  pose proof derivative_at_eq_imp_diff_const g f' f f' a b H7 H8 H9 H10 as [c H11].
  assert (H12 : 1 ∈ [a, b]) by (unfold a, b; solve_R).
  assert (H13 : x ∈ [a, b]) by (unfold a, b; solve_R).
  specialize (H11 1 H12) as H14.
  specialize (H11 x H13) as H15.
  unfold g in H14, H15.
  rewrite Rmult_1_l, H3, Rplus_0_l in H14. rewrite H15, H14. reflexivity.
Qed.