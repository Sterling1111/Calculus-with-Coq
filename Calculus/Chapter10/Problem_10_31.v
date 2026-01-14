From Calculus.Chapter10 Require Import Prelude.
Open Scope R_scope.

Lemma lemma_10_31 : forall f g,
  differentiable f -> differentiable g -> f 0 = 0 /\ g 0 = 0 ->
  (forall x, x = f x * g x) -> False.
Proof.
  intros f g H1 H2 [H3 H4] H5.
  apply differentiable_imp_derivative in H1 as [f' H1].
  apply differentiable_imp_derivative in H2 as [g' H2].
  set (h := λ x, f x * g x - x).
  assert (⟦ der ⟧ h = (λ x, f' x * g x + f x * g' x - 1)) as H6 by (unfold h; auto_diff).
  assert (h 0 = 0) as H7 by (unfold h; rewrite H3, H4; lra).
  assert (forall x, h x = 0) as H8.
  { intros x. unfold h. specialize (H5 x). lra. }
  assert (⟦ der ⟧ h = λ _ : ℝ, 0) as H9.
  { replace h with (λ _ : ℝ, 0) by (extensionality x; auto). auto_diff. }
  pose proof derivative_unique h (λ _ : ℝ, 0) (λ x : ℝ, f' x * g x + f x * g' x - 1) H9 H6 as H10.
  pose proof (equal_f H10 0) as H11. simpl in H11.
  rewrite H3, H4, Rmult_0_l, Rmult_0_r, Rplus_0_l, Rminus_0_l in H11.
  lra.
Qed.