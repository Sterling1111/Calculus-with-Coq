From Lib Require Import Imports Notations Integral Derivative Functions Continuity Taylor
                        Limit Sets Reals_util Inverse Trigonometry Sums Rational Binomial Tactics Interval.
Import IntervalNotations SetNotations SumNotations FunctionNotations 
       DerivativeNotations LimitNotations Choose_Notations RationalNotations.

Open Scope R_scope.
Open Scope rational_scope.

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

Lemma nth_derive_f_n_0 : ∀ n k,
  (k > 2 * n)%nat -> ⟦ Der ^ k ⟧ (f n) = (fun _ => 0).
Proof.
  intros n k H1. apply nth_derivative_imp_nth_derive.
  rewrite f_n_is_polynomial.
  replace (λ _ : ℝ, 0) with (λ _ : ℝ, 1 / n! * 0) by (extensionality x; lra).
  apply nth_derivative_mult_const_l.
  replace ( λ _ : ℝ, 0) with (fun x : R => ∑ n (2 * n) (λ i, 0)) by (extensionality x; rewrite sum_f_0; auto; lia).
  apply nth_derivative_sum; try lia.
  intros j H2. 
  replace (λ _ : ℝ, 0) with (fun x : R => (-1) ^ (j - n) * INR (n ∁ (j - n)) * 0) by (extensionality x; lra).
  apply nth_derivative_mult_const_l.
  apply nth_derivative_pow_gt; try lia.
Qed.

Lemma f_n_differentiable : ∀ n,
  differentiable (f n).
Proof.
  intros n. rewrite f_n_is_polynomial.
  intros x. apply differentiable_at_mult_const_l. apply differentiable_at_sum; try lia.
  intros k H1. apply differentiable_at_mult_const_l. apply differentiable_at_pow.
Qed.

Lemma f_n_nth_differentiable : ∀ n k,
  nth_differentiable k (f n).
Proof.
  intros n k. rewrite f_n_is_polynomial. apply nth_differentiable_mult_const_l.
  apply nth_derivative_imp_nth_differentiable with (fn := fun x => ∑ n (2 * n) (fun i => (⟦ Der ^ k ⟧ (fun x0 => (-1) ^ (i - n) * INR (n ∁ (i - n)) * x0 ^ i)) x)).
  apply nth_derivative_sum; try lia.
  intros l Hl. apply nth_derive_spec. apply nth_differentiable_mult_const_l.
  replace (λ x : ℝ, x ^ l) with (λ x : ℝ, (x - 0) ^ l).
  2: { extensionality x0. rewrite Rminus_0_r. reflexivity. }
  apply nth_differentiable_pow_shift.
Qed.

Lemma f_n_derivatives_at_0_are_integers : ∀ (n k: nat) (r : R),
  ⟦ Der ^ k 0 ⟧ (f n) = r -> is_integer r.
Proof.
  intros n k r H1.
  rewrite f_n_is_polynomial in H1.
  rewrite nth_derive_mult_const_l in H1.
  2 : { 
    apply nth_derivative_imp_nth_differentiable with (fn := fun x => ∑ n (2 * n) (fun i => (⟦ Der ^ k ⟧ (fun x0 => (-1) ^ (i - n) * INR (n ∁ (i - n)) * x0 ^ i)) x)).
    apply nth_derivative_sum; try lia.
    intros l H2. apply nth_derive_spec. apply nth_differentiable_mult_const_l.
    replace (λ x : ℝ, x ^ l) with (λ x : ℝ, (x - 0) ^ l).
    2: { extensionality x0. rewrite Rminus_0_r. reflexivity. }
    apply nth_differentiable_pow_shift. 
  }
  rewrite nth_derive_sum in H1; try lia.
  2 : { 
    intros j. apply nth_differentiable_mult_const_l. 
    replace (λ x : ℝ, x ^ j) with (λ x : ℝ, (x - 0) ^ j).
    2: { extensionality x0. rewrite Rminus_0_r. reflexivity. }
    apply nth_differentiable_pow_shift. 
  }
  replace (λ k0 : ℕ, (⟦ Der^k ⟧ (λ x : ℝ, (-1) ^ (k0 - n) * n ∁ (k0 - n) * x ^ k0)) 0) with (λ k0 : ℕ, (-1) ^ (k0 - n) * n ∁ (k0 - n) * (⟦ Der^k 0 ⟧ (λ x : ℝ, x ^ k0))) in H1.
  2 : { 
    extensionality k0. rewrite nth_derive_mult_const_l. auto. 
    replace (λ x : ℝ, x ^ k0) with (λ x : ℝ, (x - 0) ^ k0).
    2: { extensionality x0. rewrite Rminus_0_r. reflexivity. }
    apply nth_differentiable_pow_shift. 
  }
  pose proof nth_derivative_pow as H2.
  pose proof nth_derivative_pow_gt as H3.
  rewrite <- H1.
  rewrite r_mult_sum_f_i_n_f_l.
  apply is_integer_sum; try lia.
  intros k0 H4.
  rewrite nth_derive_at_zero_pow.
  destruct (Nat.eq_dec k0 k) as [H5 | H5].
  - subst k0.
    pose proof (fact_div'' k n ltac:(lia)) as [m H6].
    replace (1 / n! * ((-1) ^ (k - n) * n ∁ (k - n) * INR (fact k))) with (((-1) ^ (k - n) * INR (n ∁ (k - n))) * INR m).
    2 : {
      rewrite H6. rewrite mult_INR.
      field. apply INR_fact_neq_0.
    }
    apply is_integer_mult.
    + apply is_integer_mult.
      * apply is_integer_pow. exists (-1)%Z. reflexivity.
      * exists (Z.of_nat (n ∁ (k - n))). apply INR_IZR_INZ.
    + exists (Z.of_nat m). apply INR_IZR_INZ.
  - replace (1 / n! * ((-1) ^ (k0 - n) * n ∁ (k0 - n) * 0)) with 0 by lra.
    exists 0%Z. reflexivity.
Qed.

Lemma f_n_sym : forall n x, f n x = f n (1 - x).
Proof.
  intros n x. unfold f. f_equal.
  replace (1 - (1 - x)) with x by lra.
  rewrite Rmult_comm. reflexivity.
Qed.

Lemma f_n_inf_differentiable : forall n, inf_differentiable (f n).
Proof. intros n k. apply f_n_nth_differentiable. Qed.

Lemma f_n_derivatives_at_1_are_integers : ∀ (n k: nat) (r : R),
  ⟦ Der ^ k 1 ⟧ (f n) = r -> is_integer r.
Proof.
  intros n k r H1.
  assert (H2 : f n = fun x => f n (1 - x)).
  { extensionality x. apply f_n_sym. }
  rewrite H2 in H1.
  unfold nth_derive_at in H1.
  rewrite nth_derive_1_minus_x in H1.
  2 : { apply f_n_inf_differentiable. }
  replace (1 - 1) with 0 in H1 by lra.
  pose proof f_n_derivatives_at_0_are_integers n k (⟦ Der^k 0 ⟧ (f n)) ltac:(reflexivity) as H3.
  rewrite <- H1.
  apply is_integer_mult.
  - apply is_integer_pow. exists (-1)%Z. reflexivity.
  - unfold nth_derive_at in H3. apply H3.
Qed.

Theorem theorem_16_1 : π ∉ ℚ.
Proof.
  apply rational_iff, irrational_square_imp_irrational. intros H1.
  assert (H2 : π ^ 2 > 0) by (pose proof π_pos; nra).
  pose proof rational_representation_positive (π ^ 2) H1 H2 as [a [b [H3 [H4 H5]]]].
  clear H1 H2. rename H3 into H1. rename H4 into H2. rename H5 into H3.
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
      apply is_integer_sum; try lia. intros k H4. rewrite <- Rmult_assoc. apply is_integer_mult.
      - replace (π ^ (2 * n - 2 * k)) with ((π ^ 2) ^ (n - k)). 2 : { rewrite <- pow_mult. f_equal. lia. }
        rewrite H1. rewrite Rmult_comm. rewrite Rmult_assoc. apply is_integer_mult.
        -- apply is_integer_pow. exists (-1)%Z. reflexivity.
        -- rewrite Rdiv_pow_distr; auto. replace (a ^ (n - k) / b ^ (n - k) * b ^ n) with (a^(n-k) * ((b^n) / (b^(n-k)))) by lra.
           rewrite <- pow_div_sub; solve_R. replace (n - (n - k))%nat with k by lia.
           apply is_integer_mult; apply is_integer_pow; [ exists a | exists b ]; reflexivity.
      - apply (f_n_derivatives_at_0_are_integers n (2 * k)); auto.
    }
    assert (H5 : is_integer (G 1)).
    {
      unfold G. rewrite r_mult_sum_f_i_n_f_l.
      apply is_integer_sum; try lia. intros k H5. rewrite <- Rmult_assoc. apply is_integer_mult.
      - replace (π ^ (2 * n - 2 * k)) with ((π ^ 2) ^ (n - k)). 2 : { rewrite <- pow_mult. f_equal. lia. }
        rewrite H1. rewrite Rmult_comm. rewrite Rmult_assoc. apply is_integer_mult.
        -- apply is_integer_pow. exists (-1)%Z. reflexivity.
        -- rewrite Rdiv_pow_distr; auto. replace (a ^ (n - k) / b ^ (n - k) * b ^ n) with (a^(n-k) * ((b^n) / (b^(n-k)))) by lra.
           rewrite <- pow_div_sub; solve_R. replace (n - (n - k))%nat with k by lia.
           apply is_integer_mult; apply is_integer_pow; [ exists a | exists b ]; reflexivity.
      - apply (f_n_derivatives_at_1_are_integers n (2 * k)); auto.
    }
    assert (H6 : ⟦ der ⟧ G = G').
    {
      unfold G, G'.
      apply derive_spec.
      - intros x. apply differentiable_at_mult_const_l. apply differentiable_at_sum; try lia.
        intros k H6. apply differentiable_at_mult_const_l.
        apply nth_differentiable_at_imp_differentiable_at with (n := 1%nat); try lia.
        apply nth_differentiable_imp_nth_differentiable_at with (n := 1%nat); try lia.
        apply nth_derive_nth_differentiable. apply f_n_nth_differentiable.
      - rewrite derive_mult_const_l.
        2 : {
            intros x. apply differentiable_at_sum; try lia.
            intros k H6. apply differentiable_at_mult_const_l.
            apply nth_differentiable_at_imp_differentiable_at with (n := 1%nat); try lia. 
            apply nth_differentiable_imp_nth_differentiable_at with (n := 1%nat); try lia.
            apply nth_derive_nth_differentiable. apply f_n_nth_differentiable.
        }
        extensionality x. apply Rmult_eq_compat_l.
        rewrite derive_sum; try lia. 2 : { intros k H7. apply differentiable_mult_const_l. apply nth_differentiable_imp_differentiable with (n:=1%nat); try lia. apply nth_derive_nth_differentiable. apply f_n_nth_differentiable. }
        apply sum_f_equiv; try lia. intros k H7.
        rewrite derive_mult_const_l. 2 : { apply nth_differentiable_imp_differentiable with (n:=1%nat); try lia. apply nth_derive_nth_differentiable. apply f_n_nth_differentiable. }
        apply Rmult_eq_compat_l. 
        rewrite nth_derive_add with (n := 1%nat). replace (1 + 2 * k)%nat with (2 * k + 1)%nat by lia. reflexivity.
    }
    assert (H7 : ⟦ der ⟧ G' = G'').
    {
      unfold G', G''.
      apply derive_spec.
      - intros x. apply differentiable_at_mult_const_l. apply differentiable_at_sum; try lia.
        intros k H7. apply differentiable_at_mult_const_l.
        apply nth_differentiable_at_imp_differentiable_at with (n := 1%nat); try lia.
        apply nth_differentiable_imp_nth_differentiable_at with (n := 1%nat); try lia.
        apply nth_derive_nth_differentiable. apply f_n_nth_differentiable.
      - rewrite derive_mult_const_l.
        2 : {
            intros x. apply differentiable_at_sum; try lia.
            intros k H7. apply differentiable_at_mult_const_l.
            apply nth_differentiable_at_imp_differentiable_at with (n := 1%nat); try lia. 
            apply nth_differentiable_imp_nth_differentiable_at with (n := 1%nat); try lia.
            apply nth_derive_nth_differentiable. apply f_n_nth_differentiable.
        }
        extensionality x. apply Rmult_eq_compat_l.
        rewrite derive_sum; try lia. 2 : { intros k H8. apply differentiable_mult_const_l. apply nth_differentiable_imp_differentiable with (n:=1%nat); try lia. apply nth_derive_nth_differentiable. apply f_n_nth_differentiable. }
        apply sum_f_equiv; try lia. intros k H8.
        rewrite derive_mult_const_l. 2 : { apply nth_differentiable_imp_differentiable with (n:=1%nat); try lia. apply nth_derive_nth_differentiable. apply f_n_nth_differentiable. }
        apply Rmult_eq_compat_l. 
        rewrite nth_derive_add with (n := 1%nat). replace (1 + (2 * k + 1))%nat with (2 * k + 2)%nat by lia. reflexivity.
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
        assert (H9 : ∀ i : ℕ, (i < n)%nat -> A i + B (i + 1)%nat = 0). 
        {
          intros i H9. unfold A, B. replace (2 * (i + 1))%nat with (2 * i + 2)%nat by lia.
          replace (b ^ n * ((-1) ^ i * π ^ (2 * n - 2 * i) * (⟦ Der^(2 * i + 2) x ⟧ (f n))) + π ^ 2 * (b ^ n * ((-1) ^ (i + 1) * π ^ (2 * n - (2 * i + 2)) * (⟦ Der^(2 * i + 2) x ⟧ (f n))))) with
          ((b ^ n * (⟦ Der^(2 * i + 2) x ⟧ (f n))) * ((-1) ^ i * π ^ (2 * n - 2 * i) + π ^ 2 * ((-1) ^ (i + 1) * π ^ (2 * n - (2 * i + 2))))) by lra.
          apply Rmult_eq_0_compat_l. replace ((2 * n - 2 * i)%nat) with (2 * n - (2 * i + 2) + 2)%nat by lia.
          replace (i + 1)%nat with (1 + i)%nat by lia. repeat rewrite pow_add. lra.
        }
        assert (H10 : ∀ i : ℕ, (i >= n)%nat → A i + B (i + 1)%nat = 0).
        {
          intros i H10.
          unfold A, B.
          replace (2 * (i + 1))%nat with (2 * i + 2)%nat by lia.
          rewrite nth_derive_f_n_0; try lia.
          lra.
        }
        rewrite sum_f_plus; try lia.
        assert (H11 : ∑ 0 n (λ i : ℕ, A i + B i) = ∑ 0 n (λ i : ℕ, B i - B (i + 1)%nat)).
        { 
          apply sum_f_equiv; try lia.
          intros k H11.
          assert (H12 : (k < n)%nat \/ k = n) by lia.
          destruct H12 as [H12 | H12].
          - specialize (H9 k H12). lra.
          - subst. specialize (H10 n ltac:(lia)). lra. 
        }
        rewrite H11.
        rewrite sum_f_0_n_fi_minus_fSi. replace (B (n + 1)%nat) with (0).
        2 : { unfold B. rewrite nth_derive_f_n_0; try lia. lra. }
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
        apply f_n_differentiable. apply differentiable_comp. apply differentiable_sin. apply differentiable_mult_const_l.
        apply differentiable_id.
      - apply derivative_imp_derivative_on; try lra; auto. apply differentiable_domain_closed; lra.
    }
    assert (H11 : H 1 - H 0 = π * (G 1 + G 0)).
    { unfold H. rewrite Rmult_1_r, Rmult_0_r. rewrite sin_0, sin_π, cos_0, cos_π. lra. }

    rewrite H11 in H10. rewrite theorem_13_6_b in H10; try lra.
    2 : {
       apply theorem_13_3; try lra. apply differentiable_on_imp_continuous_on; try lra. apply differentiable_imp_differentiable_on; try lra.
       replace (λ x : ℝ, a ^ n * f n x * sin (π * x)) with (λ x : ℝ, a ^ n * (f n x * sin (π * x))).
       2 : { extensionality x; lra. } apply differentiable_mult_const_l. apply differentiable_mult.
      apply f_n_differentiable. apply differentiable_comp. apply differentiable_sin. apply differentiable_mult_const_l.
      apply differentiable_id. apply differentiable_domain_closed; lra.
    }
    pose proof π_pos as H12.
    apply Rmult_eq_compat_r with (r := 1 / π) in H10; try lra. field_simplify in H10; try lra.
    rewrite <- theorem_13_6_b in H10; try lra.
    2 : {
      apply theorem_13_3; try lra. apply differentiable_on_imp_continuous_on; try lra. apply differentiable_imp_differentiable_on; try lra.
      replace (λ x : ℝ, a ^ n * f n x * sin (π * x)) with (λ x : ℝ, a ^ n * (f n x * sin (π * x))).
      2 : { extensionality x; lra. } apply differentiable_mult_const_l. apply differentiable_mult.
      apply f_n_differentiable. apply differentiable_comp. apply differentiable_sin. apply differentiable_mult_const_l.
      apply differentiable_id. apply differentiable_domain_closed; lra.
    }
    replace (λ x : ℝ, π * (a ^ n * f n x * sin (π * x))) with (λ x : ℝ, π * a ^ n * f n x * sin (π * x)) in H10.
    2 : { extensionality x; lra. }
    rewrite H10.
    apply is_integer_plus; auto.
  }
  assert (H5 : ∀ n x, (n > 0)%nat -> 0 < x < 1 -> 0 < π * a^n * f n x * sin (π * x) < π * a^n / n!).
  {
    intros n x H5 H6. pose proof π_pos as H7. pose proof Rpow_gt_0 n (IZR a) H2 as H8.
    assert (H9 : 0 < sin (π * x) <= 1) by (apply sin_pi_x_bounds; auto). pose proof f_bounds n x H5 H6 as [H10 H11]. split; try lra.
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
         apply f_n_differentiable. apply differentiable_comp. apply differentiable_sin. apply differentiable_mult_const_l.
         apply differentiable_id.
    - pose proof integral_bounds_strong_open 0 1 (λ x, π * a^n * f n x * sin (π * x)) 0 (π * a^n / n!) ltac:(lra) as [H7 H8]; try lra. 
      -- intros x H7. pose proof π_pos as H8. pose proof Rpow_gt_0 n a H2 as H9.
         pose proof f_bounds n x H6 ltac:(solve_R) as [H10 H11].
         assert (H12 : 0 < sin (π * x) <= 1). { apply sin_pi_x_bounds; auto. } pose proof f_bounds n x H6 H7 as [H13 H14]. split.
         ++ do 2 (apply Rmult_lt_0_compat; try nra).
         ++ apply Rmult_lt_reg_l with (r := n! / (π * a ^ n)).
            apply Rdiv_pos_pos; try nra. apply INR_fact_lt_0.
            field_simplify; try lra. 2 : { split; try lra. pose proof INR_fact_lt_0 n; lra. }
            apply Rmult_lt_reg_r with (r := 1 / n!). apply Rdiv_pos_pos; try nra. apply INR_fact_lt_0.
            field_simplify; try apply INR_fact_neq_0. nra.
      -- apply continuous_imp_continuous_on. apply differentiable_imp_continuous.
          replace (λ x : ℝ, π * a ^ n * f n x * sin (π * x)) with (λ x : ℝ, π * (a ^ n * (f n x * sin (π * x)))).
          2 : { extensionality x; lra. } do 2 apply differentiable_mult_const_l. apply differentiable_mult.
         apply f_n_differentiable. apply differentiable_comp. apply differentiable_sin. apply differentiable_mult_const_l.
         apply differentiable_id.
  }
  pose proof pow_over_factorial_tends_to_0 (a * π) (1) (ltac:(pose proof π_pos; nra)) (ltac:(lra)) as [n H7].
  assert (H8 : π * a ^ n / n! <= (a * π) ^ n / n!).
  {
    assert (n = 0 \/ n > 0)%nat as [H8 | H8] by lia.
    - subst. simpl in H7. lra.
    - apply Rmult_le_reg_l with (r := n!). apply INR_fact_lt_0. field_simplify; try apply INR_fact_neq_0.
      rewrite Rpow_mult_distr. rewrite Rmult_comm. apply Rmult_le_compat_l. apply pow_le; lra.
      rewrite <- pow_1 at 1. apply Rle_pow. pose proof π_bounds as H9. lra. lia.
  }
  assert (n <> 0)%nat as H9. { intros H9. subst. simpl in *; lra. }
  specialize (H6 n ltac:(lia)).
  apply (no_integer_between 0 (∫ 0 1 (λ x : ℝ, π * a ^ n * f n x * sin (π * x))) ltac:(lra)); auto.
Qed.