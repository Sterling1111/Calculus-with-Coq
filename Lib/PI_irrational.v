From Lib Require Import Imports Notations Integral Derivative Functions Continuity 
                          Limit Sets Reals_util Inverse Trigonometry Sums Rational Binomial Tactics.
Import IntervalNotations SetNotations Function_Notations DerivativeNotations LimitNotations Choose_Notations.

Open Scope R_scope.

Definition f n x :=
  (x^n * (1 - x)^n) / n!.

Lemma f_bounds : ∀ n x,
  (n > 0)%nat ->
  0 < x < 1 ->
  0 < f n x < 1 / n!.
Proof.
  intros n x H1.
   pose proof INR_fact_lt_0 n as H2. unfold f. split.
  - apply Rdiv_pos_pos; auto.
    apply Rmult_pos_pos; apply Rpow_gt_0; lra.
  - apply Rmult_lt_reg_l with (r := n!); auto.
    field_simplify; try lra. assert (H3 : x^n < 1). { apply Rpow_lt_1; auto. }
    assert (H4 : (1 - x)^n < 1). { apply Rpow_lt_1. lra. lia. }
    rewrite <- Rmult_1_r. apply Rmult_gt_0_lt_compat; try lra.
    apply Rpow_gt_0; lra.
Qed.

Lemma f_n_0 : ∀ n,
  (n > 0)%nat -> f n 0 = 0.
Proof.
  intros n H1. unfold f. rewrite pow_i; try lia. lra.
Qed.

Lemma f_n_1 : ∀ n,
  (n > 0)%nat -> f n 1 = 0.
Proof.
  intros n H1. unfold f. rewrite pow1. rewrite Rminus_diag. rewrite pow_i; try lia. lra.
Qed.

Lemma one_minus_x_pow_n : forall n x,
  (1 - x) ^ n = ∑ 0 n (fun k => ((-1) ^ k * INR (n ∁ k)) * x ^ k).
Proof.
  intros n x.
  pose proof Binomial_Theorem 1 (-x) n as H1.
  replace (1 + - x) with (1 - x) in H1 by lra.
  rewrite H1.
  apply sum_f_equiv; [lia |].
  intros k H2.
  rewrite pow1. rewrite Rmult_1_r.
  replace (-x) with (-1 * x) by lra.
  rewrite Rpow_mult_distr.
  lra.
Qed.

Lemma x_n_mult_one_minus_x_pow_n : forall n x,
  x ^ n * (1 - x) ^ n = ∑ n (2 * n) (fun i => ((-1) ^ (i - n) * INR (n ∁ (i - n))) * x ^ i).
Proof.
  intros n x.
  rewrite one_minus_x_pow_n.
  rewrite r_mult_sum_f_i_n_f_l.
  rewrite sum_f_reindex' with (s := n).
  replace (2 * n)%nat with (n + n)%nat by lia.
  apply sum_f_equiv; [lia |].
  intros k H1.
  rewrite Rmult_assoc.
  rewrite (Rmult_comm (x^n)).
  repeat rewrite Rmult_assoc.
  rewrite <- pow_add.
  replace (k - n + n)%nat with k by lia.
  reflexivity.
Qed.

Lemma f_n_is_polynomial : ∀ n,
  f n = (fun x => (1 / n!) * ∑ n (2 * n) (fun i => ((-1) ^ (i - n) * INR (n ∁ (i - n))) * x ^ i)).
Proof.
  intros n. extensionality x.
  unfold f.
  rewrite x_n_mult_one_minus_x_pow_n.
  lra.
Qed.

Lemma nth_Derive_f_n_0 : ∀ n k,
  (k > 2 * n)%nat -> ⟦ Der ^ k ⟧ (f n) = (fun _ => 0).
Proof.
  intros n k H1.
  rewrite f_n_is_polynomial.
  rewrite nth_Derive_mult_const.
  rewrite nth_Derive_sum; try lia.
  extensionality x. apply Rmult_eq_0_compat_l.
  rewrite sum_f_reindex with (s := n); try lia.
  rewrite Nat.sub_diag. replace (2 * n - n)%nat with n by lia.
  rewrite sum_f_0; auto; try lia. intros m H2. rewrite nth_Derive_mult_const.
  rewrite nth_Derive_pow_gt; try lia. lra. apply nth_differentiable_pow. intros m.
  apply nth_differentiable_mult_const_l. apply nth_differentiable_pow.
  apply nth_differentiable_sum; try lia. intros m. 
  apply nth_differentiable_mult_const_l. apply nth_differentiable_pow.
Qed.

Lemma f_n_differentiable : ∀ n,
  differentiable (f n).
Proof.
  intros n. rewrite f_n_is_polynomial.
  apply differentiable_mult_const_l. apply differentiable_sum; try lia.
  intros k H1. apply differentiable_mult_const_l. apply differentiable_pow.
Qed.

Lemma f_n_nth_differentiable : ∀ n k,
  nth_differentiable k (f n).
Proof.
  intros n k. rewrite f_n_is_polynomial. apply nth_differentiable_mult_const_l.
  apply nth_differentiable_sum; try lia.
  intros l. apply nth_differentiable_mult_const_l. apply nth_differentiable_pow.
Qed.

Lemma f_n_derivatives_at_0_are_integers : ∀ (n k: nat) (r : R),
  ⟦ der ^ k 0 ⟧ (f n) = r -> is_integer r.
Proof.
  intros n k r H1.
  rewrite f_n_is_polynomial in H1.
  pose proof nth_derivative_x_i_at_0 k k as H2.
  
Admitted.

Lemma f_n_derivatives_at_1_are_integers : ∀ (n k: nat) (r : R),
  ⟦ der ^ k 1 ⟧ (f n) = r -> is_integer r.
Proof.
Admitted.

Lemma pow_over_factorial_tends_to_0 : ∀ x ε,
  x > 0 -> ε > 0 -> ∃ n, x^n / n! < ε.
Proof.
Admitted.

Theorem theorem_16_1 : irrational π.
Proof.
  apply irrational_square_imp_irrational. intros [a [b H1]].
  assert (exists a b : Z, π^2 = (a / b) /\ a > 0 /\ b > 0) as [a' [b' [H2 [H3 H4]]]].
  {
    pose proof π_pos as H2. assert (H3 : π^2 > 0) by nra.
    pose proof Rtotal_order a 0 as [H4 | [H4 | H4]]; pose proof Rtotal_order b 0 as [H5 | [H5 | H5]];
    pose proof Rdiv_neg_neg a b as H6; pose proof Rdiv_pos_pos a b as H7; pose proof Rdiv_neg_pos a b as H8; pose proof Rdiv_pos_neg a b as H9;
    try nra; try (rewrite H5 in H1; rewrite Rdiv_0_r in H1; lra).
    - exists (- a)%Z, (- b)%Z. repeat rewrite opp_IZR. split; try nra. rewrite H1. field. nra.
    - exists a, b. auto.
  }
  clear a b H1. rename a' into a. rename b' into b. rename H2 into H1. rename H3 into H2. rename H4 into H3.
  assert (H4 : forall n, is_integer (∫ 0 1 (λ x, π * a^n * f n x * sin (π * x)))).
  {
    intros n.
    set (G := λ x, b^n * ∑ 0 n (λ k, (-1)^k * π^(2*n - 2*k) * (⟦ Der ^ (2*k) x ⟧ (f n)))).
    set (G' := λ x, b^n * ∑ 0 n (λ k, (-1)^k * π^(2*n - 2*k) * (⟦ Der ^ (2*k + 1) x ⟧ (f n)))).
    set (G'' := λ x, b^n * ∑ 0 n (λ k, (-1)^k * π^(2*n - 2*k) * (⟦ Der ^ (2*k + 2) x ⟧ (f n)))).
    set (H := λ x, (G' x) * sin (π*x) - π * ((G x) * cos (π*x))).
    set (H' := λ x, ((G'' x) * sin (π*x) + G'(x) * π * cos (π*x)) - (π * ((G' x) * cos (π*x) - π * (G x) * sin (π*x)))).

    assert (H4 : is_integer (G 0)).
    {
      unfold G. rewrite r_mult_sum_f_i_n_f_l.
      apply is_integer_sum. intros k H4. rewrite <- Rmult_assoc. apply is_integer_mult.
      - replace (π ^ (2 * n - 2 * k)) with ((π ^ 2) ^ (n - k)). 2 : { rewrite <- pow_mult. f_equal. lia. }
        rewrite H1. rewrite Rmult_comm. rewrite Rmult_assoc. apply is_integer_mult.
        -- apply is_integer_pow. exists (-1)%Z. reflexivity.
        -- rewrite Rdiv_pow_distr; auto. replace (a ^ (n - k) / b ^ (n - k) * b ^ n) with (a^(n-k) * ((b^n) / (b^(n-k)))) by lra.
           rewrite <- pow_div_sub; solve_R. replace (n - (n - k))%nat with k. 2 : { apply INR_le in H4. lia. }
           apply is_integer_mult; apply is_integer_pow; [ exists a | exists b ]; reflexivity.
      - apply (f_n_derivatives_at_0_are_integers n (2 * k)). pose proof nth_Derive_at_eq (2 * k) 0 (f n) as H6.
        pose proof f_n_differentiable n as H7. pose proof differentiable_imp_exists_derivative (f n) H7 as [f' H8].
        specialize (H6 f'). apply nth_Derive_at_spec; auto. apply f_n_nth_differentiable.
    }
    assert (H5 : is_integer (G 1)).
    {
      unfold G. rewrite r_mult_sum_f_i_n_f_l.
      apply is_integer_sum. intros k H5. rewrite <- Rmult_assoc. apply is_integer_mult.
      - replace (π ^ (2 * n - 2 * k)) with ((π ^ 2) ^ (n - k)). 2 : { rewrite <- pow_mult. f_equal. lia. }
        rewrite H1. rewrite Rmult_comm. rewrite Rmult_assoc. apply is_integer_mult.
        -- apply is_integer_pow. exists (-1)%Z. reflexivity.
        -- rewrite Rdiv_pow_distr; auto. replace (a ^ (n - k) / b ^ (n - k) * b ^ n) with (a^(n-k) * ((b^n) / (b^(n-k)))) by lra.
           rewrite <- pow_div_sub; solve_R. replace (n - (n - k))%nat with k. 2 : { apply INR_le in H5. lia. }
           apply is_integer_mult; apply is_integer_pow; [ exists a | exists b ]; reflexivity.
      - apply (f_n_derivatives_at_1_are_integers n (2 * k)). pose proof nth_Derive_at_eq (2 * k) 1 (f n) as H6.
        pose proof f_n_differentiable n as H7. pose proof differentiable_imp_exists_derivative (f n) H7 as [f' H8].
        specialize (H6 f'). apply nth_Derive_at_spec; auto. apply f_n_nth_differentiable.
    }
    assert (H6 : ⟦ der ⟧ G = G').
    {
      unfold G, G'.
      apply theorem_10_5'. assert (H6 : forall k, differentiable (nth_Derive_at (2 * k) (f n))).
      { intros k. apply nth_differentiable_imp_differentiable with (n := 1%nat); try lia. apply nth_Derive_nth_differentiable. apply f_n_nth_differentiable. }
      apply Derive_spec.
      - apply differentiable_sum; try lia. intros k. apply differentiable_mult_const_l; auto.
      - rewrite Derive_sum; try lia. 2 : { intros k H7. apply differentiable_mult_const_l; auto. }
        extensionality x. apply sum_f_equiv; try lia. intros k H7.
        rewrite Derive_mult_const; auto. apply Rmult_eq_compat_l. rewrite Derive_nth_Derive.
        replace (S (2 * k)) with (2 * k + 1)%nat by lia. reflexivity.
    }
    assert (H7 : ⟦ der ⟧ G' = G'').
    {
      unfold G', G''.
      apply theorem_10_5'. assert (H7 : forall k, differentiable (nth_Derive_at (2 * k + 1) (f n))).
      { intros k. apply nth_differentiable_imp_differentiable with (n := 1%nat); try lia. apply nth_Derive_nth_differentiable. apply f_n_nth_differentiable. }
      apply Derive_spec.
      - apply differentiable_sum; try lia. intros k. apply differentiable_mult_const_l; auto.
      - rewrite Derive_sum; try lia. 2 : { intros k H8. apply differentiable_mult_const_l; auto. }
        extensionality x. apply sum_f_equiv; try lia. intros k H8.
        rewrite Derive_mult_const; auto. apply Rmult_eq_compat_l. rewrite Derive_nth_Derive.
        replace (S (2 * k + 1)) with (2 * k + 2)%nat by lia. reflexivity.
    }
    assert (H8 : ⟦ der ⟧ H = H') by (unfold H, H'; auto_diff).
    assert (H9 : H' = (fun x => π^2 * (a^n * f n x * sin (π * x)))).
    {
      unfold H'. extensionality x.
      assert (H9 : G'' x + π^2 * (G x) = π^2 * a^n * f n x).
      {
        unfold G, G''.
        rewrite r_mult_sum_f_i_n_f_l. do 2 rewrite r_mult_sum_f_i_n_f_l.
        set (A := fun i => b ^ n * ((-1) ^ i * π ^ (2 * n - 2 * i) * (⟦ Der^(2 * i + 2) x ⟧ (f n)))).
        set (B := fun i => π ^ 2 * (b ^ n * ((-1) ^ i * π ^ (2 * n - 2 * i) * (⟦ Der^(2 * i) x ⟧ (f n))))).
        assert (H9 : ∀ i : ℕ, A i + B (i + 1)%nat = 0). 
        {
          intros i. unfold A, B. replace (2 * (i + 1))%nat with (2 * i + 2)%nat by lia.
          replace (b ^ n * ((-1) ^ i * π ^ (2 * n - 2 * i) * (⟦ Der^(2 * i + 2) x ⟧ (f n))) + π ^ 2 * (b ^ n * ((-1) ^ (i + 1) * π ^ (2 * n - (2 * i + 2)) * (⟦ Der^(2 * i + 2) x ⟧ (f n))))) with
          ((b ^ n * (⟦ Der^(2 * i + 2) x ⟧ (f n))) * ((-1) ^ i * π ^ (2 * n - 2 * i) + π ^ 2 * ((-1) ^ (i + 1) * π ^ (2 * n - (2 * i + 2))))) by lra.
          apply Rmult_eq_0_compat_l. admit.
        }
        rewrite sum_f_plus; try lia. 
        replace (λ i : ℕ, A i + B i) with (λ i : ℕ, B i - B (i + 1)%nat).
        2 : { extensionality i. specialize (H9 i). lra. }
        rewrite sum_f_0_n_fi_minus_fSi. replace (B (n + 1)%nat) with (0).
        2 : { unfold B. rewrite nth_Derive_f_n_0; try lia. lra. }
        rewrite Rminus_0_r. unfold B. rewrite pow_O. rewrite Rmult_1_l. rewrite Nat.mul_0_r.
        rewrite Nat.sub_0_r. replace (⟦ Der^0 x ⟧ (f n)) with (f n x) by reflexivity.
        rewrite Rmult_assoc. apply Rmult_eq_compat_l. rewrite <- Rmult_assoc.
        apply Rmult_eq_compat_r. rewrite pow_mult, H1. rewrite Rdiv_pow_distr; auto. field. apply pow_nonzero; lra.
      }
      nra.
    }
    assert (H10 : ∫ 0 1 (λ x : ℝ, π ^ 2 * (a ^ n * f n x * sin (π*x))) = H 1 - H 0).
    {
      rewrite <- H9.
      apply FTC2.
      - lra.
      - rewrite H9. apply continuous_imp_continuous_on. apply differentiable_imp_continuous.
        replace (λ x : ℝ, π ^ 2 * (a ^ n * f n x * sin (π * x))) with (λ x : ℝ, π ^ 2 * (a ^ n * (f n x * sin (π * x)))).
        2 : { extensionality x; lra. } do 2 apply differentiable_mult_const_l. apply differentiable_mult.
        apply f_n_differentiable. apply differentiable_comp. apply sin_differentiable. apply differentiable_mult_const_l.
        apply differentiable_id.
      - apply derivative_imp_derivative_on; try lra; auto.
    }
    assert (H11 : H 1 - H 0 = π * (G 1 + G 0)).
    { unfold H. rewrite Rmult_1_r, Rmult_0_r. rewrite sin_0, sin_π, cos_0, cos_π. lra. }

    rewrite H11 in H10. rewrite theorem_13_6_b in H10; try lra.
    2 : {
       apply theorem_13_3; try lra. apply theorem_9_1_d; try lra. apply differentiable_imp_differentiable_on; try lra.
       replace (λ x : ℝ, a ^ n * f n x * sin (π * x)) with (λ x : ℝ, a ^ n * (f n x * sin (π * x))).
       2 : { extensionality x; lra. } apply differentiable_mult_const_l. apply differentiable_mult.
      apply f_n_differentiable. apply differentiable_comp. apply sin_differentiable. apply differentiable_mult_const_l.
      apply differentiable_id.
    }
    pose proof π_pos as H12.
    apply Rmult_eq_compat_r with (r := 1 / π) in H10; try lra. field_simplify in H10; try lra.
    rewrite <- theorem_13_6_b in H10; try lra.
    2 : {
      apply theorem_13_3; try lra. apply theorem_9_1_d; try lra. apply differentiable_imp_differentiable_on; try lra.
      replace (λ x : ℝ, a ^ n * f n x * sin (π * x)) with (λ x : ℝ, a ^ n * (f n x * sin (π * x))).
      2 : { extensionality x; lra. } apply differentiable_mult_const_l. apply differentiable_mult.
      apply f_n_differentiable. apply differentiable_comp. apply sin_differentiable. apply differentiable_mult_const_l.
      apply differentiable_id.
    }
    replace (λ x : ℝ, π * (a ^ n * f n x * sin (π * x))) with (λ x : ℝ, π * a ^ n * f n x * sin (π * x)) in H10.
    2 : { extensionality x; lra. }
    rewrite H10.
    apply is_integer_plus; auto.
  }
  assert (H5 : ∀ n x, (n > 0)%nat -> 0 < x < 1 -> 0 < π * a^n * f n x * sin (π * x) < π * a^n / n!).
  {
    intros n x H5 H6. pose proof π_pos as H7. pose proof Rpow_gt_0 n (IZR a) H2 as H8.
    assert (H9 : 0 < sin (π * x) < 1) by admit. pose proof f_bounds n x H5 H6 as [H10 H11]. split; try lra.
    - do 2 (apply Rmult_lt_0_compat; try nra).
    - apply Rmult_lt_reg_l with (r := n! / (π * a ^ n)).
      apply Rdiv_pos_pos; try nra. apply INR_fact_lt_0.
      field_simplify; try lra. 2 : { split; try lra. pose proof INR_fact_lt_0 n; lra. }
      apply Rmult_lt_reg_r with (r := 1 / n!). apply Rdiv_pos_pos; try nra. apply INR_fact_lt_0.
      field_simplify; try apply INR_fact_neq_0. nra.
  }
  assert (H6 : ∀ n, (n > 0)%nat -> 0 < ∫ 0 1 (λ x, π * a^n * f n x * sin (π * x)) < π * a^n / n!).
  {
    intros n H6. split.
    - apply integral_pos'; try lra. intros x H7. assert (x = 0 \/ x = 1 \/ (0 < x < 1)) as [H8 | [H8 | H8]] by solve_R.
      -- subst. rewrite Rmult_0_r. rewrite sin_0. lra.
      -- subst. rewrite Rmult_1_r. rewrite sin_π. lra.
      -- specialize (H5 n x H6 H8). lra.
      -- exists (1/2). split; [solve_R |]. pose proof f_bounds n (1/2) H6 ltac:(lra) as [H8 _].
         replace (π * (1 / 2)) with (π / 2) by lra. rewrite sin_π_over_2. rewrite Rmult_1_r. 
         pose proof π_pos as H9. pose proof Rpow_gt_0 n a H2 as H10. apply Rmult_lt_0_compat; nra.
      -- apply continuous_imp_continuous_on. apply differentiable_imp_continuous.
         replace (λ x : ℝ, π * a ^ n * f n x * sin (π * x)) with (λ x : ℝ, π * (a ^ n * (f n x * sin (π * x)))).
         2 : { extensionality x; lra. } do 2 apply differentiable_mult_const_l. apply differentiable_mult.
         apply f_n_differentiable. apply differentiable_comp. apply sin_differentiable. apply differentiable_mult_const_l.
         apply differentiable_id.
    - pose proof integral_bounds_strong_open 0 1 (λ x, π * a^n * f n x * sin (π * x)) 0 (π * a^n / n!) ltac:(lra) as [H7 H8]; try lra. 
      -- intros x H7. pose proof π_pos as H8. pose proof Rpow_gt_0 n a H2 as H9.
         pose proof f_bounds n x H6 ltac:(solve_R) as [H10 H11].
         assert (H12 : 0 < sin (π * x) < 1) by admit. pose proof f_bounds n x H6 H7 as [H13 H14]. split.
         ++ do 2 (apply Rmult_lt_0_compat; try nra).
         ++ apply Rmult_lt_reg_l with (r := n! / (π * a ^ n)).
            apply Rdiv_pos_pos; try nra. apply INR_fact_lt_0.
            field_simplify; try lra. 2 : { split; try lra. pose proof INR_fact_lt_0 n; lra. }
            apply Rmult_lt_reg_r with (r := 1 / n!). apply Rdiv_pos_pos; try nra. apply INR_fact_lt_0.
            field_simplify; try apply INR_fact_neq_0. nra.
      -- apply continuous_imp_continuous_on. apply differentiable_imp_continuous.
          replace (λ x : ℝ, π * a ^ n * f n x * sin (π * x)) with (λ x : ℝ, π * (a ^ n * (f n x * sin (π * x)))).
          2 : { extensionality x; lra. } do 2 apply differentiable_mult_const_l. apply differentiable_mult.
         apply f_n_differentiable. apply differentiable_comp. apply sin_differentiable. apply differentiable_mult_const_l.
         apply differentiable_id.
  }
  pose proof pow_over_factorial_tends_to_0 (a * π) (1) (ltac:(pose proof π_pos; nra)) (ltac:(lra)) as [n H7].
  assert (H8 : π * a ^ n / n! < (a * π) ^ n / n!).
  {
    apply Rmult_lt_reg_l with (r := n!). apply INR_fact_lt_0.  field_simplify; try apply INR_fact_neq_0.
    rewrite Rpow_mult_distr. rewrite Rmult_comm. apply Rmult_lt_compat_l. apply pow_lt; auto.
    admit.
  }
  assert ((n = 0)%nat \/ (n > 0)%nat) as [H9 | H9] by lia.
  - subst. simpl in H7. rewrite Rdiv_1_r in H7. lra.
  - specialize (H6 n H9) as [H10 H11]. specialize (H4 n) as [c H4].
    rewrite H4 in *. assert (H12 : 0 < c < 1) by lra. 
Admitted.