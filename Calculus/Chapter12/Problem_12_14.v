From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_14_a :
  exists f, differentiable f /\ forall x, (f x)^5 + f x + x = 0.
Proof.
  set (g := fun y : R => - y ^ 5 - y).
  assert (H1 : ⟦ der ⟧ (fun y => y ^ 5) = fun y => 5 * y ^ 4) by auto_diff.
  assert (H2 : ⟦ der ⟧ (fun y => - y ^ 5) = fun y => - 5 * y ^ 4) by auto_diff.
  assert (H3 : ⟦ der ⟧ (fun y => y) = fun _ => 1) by auto_diff.
  assert (H4 : ⟦ der ⟧ g = fun y => -5 * y ^ 4 - 1) by (unfold g; auto_diff).
  assert (H5 : forall y, (fun z => -5 * z ^ 4 - 1) y < 0) by (intros; nra).
  assert (H6 : bijective g).
  {
    split. intros x _. apply Full_intro. split.
    - intros x y H7 H8 H9.
      destruct (Rtotal_order x y) as [H10 | [H10 | H10]]; auto.
      + assert (H11 : decreasing_on g [x, y]).
        { apply derivative_on_neg_imp_decreasing_on with (f' := fun z => -5 * z ^ 4 - 1); unfold g; auto_diff. }
        specialize (H11 x y ltac:(solve_R) ltac:(solve_R) H10).
        lra.
      + assert (H11 : decreasing_on g [y, x]).
        { apply derivative_on_neg_imp_decreasing_on with (f' := fun z => -5 * z ^ 4 - 1); unfold g; auto_diff. }
        specialize (H11 y x ltac:(solve_R) ltac:(solve_R) H10).
        lra.
    - intros x.
      destruct (Rtotal_order x 0) as [H7 | [H7 | H7]].
      + assert (H8 : 0 < - x + 1) by lra.
        assert (H9 : continuous_on g [0, - x + 1]) by (unfold g; auto_cont).
        assert (H10 : g (- x + 1) < x < g 0) by (unfold g; nra).
        pose proof intermediate_value_theorem_decreasing g 0 (- x + 1) x H8 H9 H10 as [y [H11 H12]].
        exists y. split; auto. apply Full_intro.
      + exists 0. split; auto. apply Full_intro. unfold g. rewrite H7. simpl. lra.
      + assert (H8 : - x - 1 < 0) by lra.
        assert (H9 : continuous_on g [- x - 1, 0]) by (unfold g; auto_cont).
        assert (H10 : g 0 < x < g (- x - 1)) by (unfold g; nra).
        pose proof intermediate_value_theorem_decreasing g (- x - 1) 0 x H8 H9 H10 as [y [H11 H12]].
        exists y. split; auto. apply Full_intro.
  }
  pose proof (exists_inverse_on_iff g ℝ ℝ) as [_ H7].
  assert (H8 : exists f, inverse g f) by auto.
  destruct H8 as [f H9].
  exists f.
  split.
  - assert (H10 : ⟦ der ⟧ f = fun x => / (-5 * (f x) ^ 4 - 1)).
    {
      apply global_inverse_theorem with (f := g) (f' := fun y => -5 * y ^ 4 - 1); auto.
      intros y. pose proof (H5 y) as H11. lra.
    }
    eapply derivative_imp_differentiable; eauto.
  - intros x.
    destruct H9 as [H11 [H12 [H13 H14]]].
    specialize (H14 x ltac:(apply Full_intro)).
    unfold g in H14.
    lra.
Qed.