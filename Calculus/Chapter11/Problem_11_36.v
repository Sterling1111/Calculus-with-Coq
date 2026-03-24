From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_36 : ∀ f n,
  (n > 1)%nat ->
  (∀ x y, |f x - f y| <= |x - y|^n) ->
  ∃ c, ∀ x, f x = c.
Proof.
  intros f n H1 H2.
  assert (H3 : ⟦ der ⟧ f = λ _, 0).
  {
    intros x.
    unfold derivative_at.
    apply limit_squeeze with (f1 := fun h => - |h| ^ (n - 1)) (f3 := fun h => |h| ^ (n - 1)) (a := -1) (b := 1).
    - lra.
    - solve_R.
    - assert (H3 : ⟦ lim 0 ⟧ (λ h : ℝ, |h|) = 0).
      { intros ε H3. exists ε. split; solve_R. }
      pose proof (limit_pow _ _ _ (n - 1) H3) as H4.
      assert (H5 : 0 ^ (n - 1) = 0).
      { rewrite pow_i; auto; lia. }
      rewrite H5 in H4.
      pose proof (limit_neg _ _ _ H4) as H6.
      replace (-0) with 0 in H6 by lra.
      exact H6.
    - assert (H3 : ⟦ lim 0 ⟧ Rabs = 0).
      { intros ε H3. exists ε. split; solve_R. }
      pose proof (limit_pow Rabs 0 0 (n - 1) H3) as H4.
      assert (H5 : 0 ^ (n - 1) = 0).
      { rewrite pow_i; auto; lia. }
      rewrite H5 in H4.
      exact H4.
    - intros h H4.
      assert (H5 : h <> 0). { intros H5. destruct H4; solve_R. }
      assert (H6 : |h| <> 0) by solve_R.
      assert (H7 : |(f (x + h) - f x) / h| <= |h| ^ (n - 1)).
      {
        rewrite Rabs_div; auto.
        specialize (H2 (x + h) x).
        replace (x + h - x) with h in H2 by lra.
        assert (H8 : |h| ^ n = |h| * |h| ^ (n - 1)).
        {
          destruct n as [| k]; [ lia |].
          replace (S k - 1)%nat with k by lia.
          simpl. lra.
        }
        rewrite H8 in H2.
        assert (H9 : |h| > 0) by solve_abs.
        apply Rmult_le_compat_r with (r := / |h|) in H2.
        - replace (|h| * |h| ^ (n - 1) * / |h|) with (|h| ^ (n - 1) * (|h| * / |h|)) in H2 by lra.
          rewrite Rinv_r in H2; auto.
          replace (|h| ^ (n - 1) * 1) with (|h| ^ (n - 1)) in H2 by lra.
          unfold Rdiv. exact H2.
        - apply Rlt_le, Rinv_0_lt_compat, H9.
      }
      solve_abs.
  }
  exists (f 0).
  intros x.
  destruct (Req_dec x 0) as [H4 | H4].
  - subst. reflexivity.
  - destruct (Rlt_dec 0 x) as [H5 | H5].
    + pose proof (derivative_zero_imp_const f 0 x H5) as [c H6].
      * apply derivative_imp_derivative_on; [| apply H3].
        intros y H7. auto_interval.
      * assert (H7 : f 0 = c) by (apply H6; solve_R).
        assert (H8 : f x = c) by (apply H6; solve_R).
        lra.
    + pose proof (derivative_zero_imp_const f x 0 ltac:(lra)) as [c H6].
      * apply derivative_imp_derivative_on; [| apply H3].
        intros y H7. auto_interval.
      * assert (H7 : f 0 = c) by (apply H6; solve_R).
        assert (H8 : f x = c) by (apply H6; solve_R).
        lra.
Qed.