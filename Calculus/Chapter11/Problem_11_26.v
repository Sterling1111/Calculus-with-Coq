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
  
Admitted.