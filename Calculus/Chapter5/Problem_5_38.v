From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_38_b :  ⟦ lim 0⁺ ⟧ (λ x : ℝ, 1 / x) = ∞.
Proof.
  unfold right_limit_to_pinf.
  intros M. exists (1 / (|M| + 1)). split.
  - apply Rdiv_pos_pos; solve_R.
  - intros x [H1 H2]. rewrite Rminus_0_r in *. apply Rmult_lt_reg_l with (r := x); auto.
    field_simplify; try lra. apply Rmult_lt_compat_r with (r := |M| + 1) in H2; solve_R.
    field_simplify in H2; lra.
Qed.

Lemma lemma_5_38_c :  forall f, 
  ⟦ lim 0⁺ ⟧ f = ∞ <-> ⟦ lim ∞ ⟧ (λ x, f (1 / x)) = ∞.
Proof.
  intros f; split; intros H1 M.
  - specialize (H1 M) as [δ [H1 H2]]. exists (1 / δ). intros x H3.
    apply H2. rewrite Rminus_0_r. pose proof Rdiv_pos_pos 1 δ ltac:(lra) ltac:(lra) as H4. split.
    -- apply Rdiv_pos_pos; lra.
    -- apply Rmult_lt_reg_r with (r := x); try lra. field_simplify; try lra.
       apply Rmult_lt_compat_r with (r := δ) in H3; try lra. field_simplify in H3; lra.
  - specialize (H1 M) as [N H2]. exists (1 / (|N| + 1)). split.
    -- apply Rdiv_pos_pos; solve_R.
    -- intros x [H3 H4]. rewrite Rminus_0_r in H3, H4. 
       specialize (H2 ((1 / x))). replace (1 / (1 / x)) with x in H2 by solve_R.
       apply H2. apply Rmult_lt_reg_r with (r := x); auto. field_simplify; try lra.
       apply Rmult_lt_compat_r with (r := |N| + 1) in H4.
       2 : { solve_R. } field_simplify in H4; solve_R.
Qed.