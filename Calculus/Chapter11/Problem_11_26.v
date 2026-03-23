From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_26 : ∀ l n,
  degree l = n ->
  let f := λ x, polynomial l x in
  (∀ x, f x >= 0) ->
  ∀ x, ∑ 0 n (λ i, ⟦ Der^i x ⟧ f) >= 0.
Proof.
  intros l n H1 f H2 x.
  set (g := λ x, ∑ 0 n (λ i, ⟦ Der^i x ⟧ f)).
  set (g' := λ x, ∑ 1 (n + 1) (λ i, ⟦ Der^i x ⟧ f)).

  replace (∑ 0 n (λ i : ℕ, ⟦ Der^i x ⟧ f)) with (g x).
  2 : { unfold g. reflexivity. }

  assert (H3 : ⟦ der ⟧ g = g').
  {
    unfold g, g'.
    apply derivative_ext with (f1' := λ x0 : ℝ, ∑ 0 n λ i : ℕ, ⟦ Der^(S i) x0 ⟧ f).
    {
      intros y. rewrite sum_f_reindex' with (s := 1%nat); try lia. rewrite Nat.add_1_r.
      apply sum_f_equiv; try lia. intros k H3. replace (S (k - 1)) with k by lia. reflexivity.
    }
    apply derivative_sum; try lia. intros k H3'. apply derive_spec; auto.
    apply inf_diff_nth_derive_diff. apply polynomial_inf_differentiable.
  }

  assert (H4 : (g - g' = f)%function).
  {
    extensionality y. unfold g, g', f.
    assert (H5 : sum_f 0 n (λ i : ℕ, ⟦ Der^i y ⟧ (λ x0 : ℝ, polynomial l x0)) - sum_f 1 (n + 1) (λ i : ℕ, ⟦ Der^i y ⟧ (λ x0 : ℝ, polynomial l x0)) = ⟦ Der^0 y ⟧ (λ x0 : ℝ, polynomial l x0) - ⟦ Der^(n+1) y ⟧ (λ x0 : ℝ, polynomial l x0)).
    {
      destruct n as [| n'].
      - simpl. rewrite sum_f_0_0, sum_f_n_n. replace 1%nat with (0+1)%nat by lia. simpl. lra.
      - replace (S n' + 1)%nat with (S (S n')) by lia.
        rewrite sum_f_Si with (i := 0%nat) (n := S n'); try lia.
        assert (H6 : sum_f 1 (S (S n')) (λ i : ℕ, ⟦ Der^i y ⟧ (λ x0 : ℝ, polynomial l x0)) = sum_f 1 (S n') (λ i : ℕ, ⟦ Der^i y ⟧ (λ x0 : ℝ, polynomial l x0)) + ⟦ Der^(S (S n')) y ⟧ (λ x0 : ℝ, polynomial l x0)).
        { apply sum_f_i_Sn_f. lia. }
        rewrite H6. lra.
    }
    rewrite H5.
    replace (⟦ Der^0 y ⟧ (λ x0 : ℝ, polynomial l x0)) with (polynomial l y) by (simpl; reflexivity).
    assert (H7 : ⟦ Der^(n+1) y ⟧ (λ x0 : ℝ, polynomial l x0) = 0).
    { apply polynomial_derive_gt_degree. lia. }
    rewrite H7. lra.
  }

  assert (H5 : g = polynomial (poly_sum_derivatives n l)).
  { extensionality y. unfold g, f. rewrite <- eval_poly_sum_derivatives. reflexivity. }

  destruct (Nat.eq_dec n 0) as [H6 | H6].
  - unfold g. rewrite H6, sum_f_0_0, nth_derive_at_0. apply H2.
  - assert (H7 : ~ is_zero_poly l).
    { intros H8. apply zero_poly_degree_0_val in H8. lia. }
    assert (H8 : Nat.Even (degree (poly_sum_derivatives n l))).
    { pose proof (poly_sum_derivatives_degree_lead n l) as [H9 _]. rewrite H9. apply polynomial_pos_imp_even; auto. }
    assert (H9 : (degree (poly_sum_derivatives n l) > 0)%nat).
    { pose proof (poly_sum_derivatives_degree_lead n l) as [H10 _]. lia. }
    assert (H10 : lead_coeff (poly_sum_derivatives n l) > 0).
    { pose proof (poly_sum_derivatives_degree_lead n l) as [_ H11]. rewrite H11. apply polynomial_pos_imp_lead_coeff_pos; auto. }
    pose proof polynomial_even_limit (poly_sum_derivatives n l) H8 H9 H10 as [H11 H12].
    assert (H13 : continuous g).
    { rewrite H5. apply continuous_polynomial. }
    rewrite <- H5 in H11, H12.
    pose proof continuous_limit_pinf_minf_global_min g H13 H11 H12 as [c H14].
    pose proof global_min_deriv_zero g g' c H3 H14 as H15.
    assert (H16 : g c - g' c = f c).
    { rewrite <- H4. reflexivity. }
    assert (H17 : f c >= 0) by apply H2.
    assert (H18 : g c >= 0) by lra.
    specialize (H14 x).
    lra.
Qed.