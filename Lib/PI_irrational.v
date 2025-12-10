From Lib Require Import Imports Notations Integral Derivative Functions Continuity Limit Sets Reals_util Inverse Trigonometry Sums Rational Binomial.
Import IntervalNotations SetNotations Function_Notations DerivativeNotations LimitNotations Choose_Notations.

Open Scope R_scope.

Local Definition f n x :=
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

Lemma f_n_derivatives_at_0_are_integers : ∀ (n k: nat) (r : R),
  ⟦ der ^ k 0 ⟧ (f n) = r -> is_integer r.
Proof.
  intros n k r H1.
  rewrite f_n_is_polynomial in H1.
  pose proof nth_derivative_x_i_at_0 k k.
  
Admitted.

Lemma f_n_symmetry : ∀ n x,
  f n x = f n (1 - x).
Proof.
  intros n x. unfold f. replace (1 - (1 - x)) with x by nra. lra.
Qed.

Lemma f_n_derivative_symmetry : ∀ f_n' (n k: nat) (x : R),
  ⟦ der ^ k ⟧ (f n) = f_n' ->
  ⟦ der ^ k x ⟧ (f n) = ((-1) ^ k) * f_n' (1 - x).
Proof.
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
  assert (a > 0 /\ b > 0) as [H2 H3] by admit.
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
      unfold G. apply is_integer_mult.
      - apply is_integer_pow; auto. exists b. reflexivity.
      - admit.
    }
    assert (H5 : is_integer (G 1)) by admit.
    assert (H6 : ⟦ der ⟧ G = G').
    {
      unfold G, G'.
      apply theorem_10_5'.
      apply Derive_spec.
      apply differentiable_sum. intros k. admit.
      rewrite sum_Derive_commute. 2 : { admit. }
      extensionality x.
      apply sum_f_equiv; try lia. intros k H6.
      admit.
    }
    assert (H7 : ⟦ der ⟧ G' = G'') by admit.
    
    assert (H8 : ⟦ der ⟧ H = H').
    {
      unfold H, H'.
      assert (H8 : ⟦ der ⟧ (fun x => sin (π*x)) = fun x => π * cos (π*x)) by admit.
      assert (H9 : ⟦ der ⟧ (fun x => cos (π*x)) = fun x => - π * sin (π*x)) by admit.
      
      apply theorem_10_3_d.
      - pose proof theorem_10_4_c G' (fun x => sin (π*x)) G'' (fun x => π * cos (π*x)) H7 H8 as H10.
        admit.
      - apply theorem_10_5'. 
        pose proof theorem_10_4_c G (fun x => cos (π*x)) G' (fun x => - π * sin (π*x)) H6 H9 as H11.
        admit.
    }
    assert (H9 : H' = (fun x => π^2 * (a^n * f n x * sin (π * x)))).
    {
      unfold H'. extensionality x. assert (H9 : G'' x + π^2 * (G x) = π^2 * a^n * f n x) by admit.
      nra.
    }
    assert (H10 : ∫ 0 1 (λ x : ℝ, π ^ 2 * (a ^ n * f n x * sin (π*x))) = H 1 - H 0).
    {
      rewrite <- H9.
      apply FTC2.
      - lra.
      - admit.
      - apply derivative_imp_derivative_on; try lra; auto.
    }
    assert (H11 : H 1 - H 0 = π * (G 1 + G 0)).
    { unfold H. rewrite Rmult_1_r, Rmult_0_r. rewrite sin_0, sin_π, cos_0, cos_π. lra. }

    rewrite H11 in H10. rewrite theorem_13_6_b in H10; try lra.
    2 : { apply theorem_13_3; try lra. admit. }
    pose proof π_pos as H12.
    apply Rmult_eq_compat_r with (r := 1 / π) in H10; try lra. field_simplify in H10; try lra.
    rewrite <- theorem_13_6_b in H10; try lra. 2 : { admit. }
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
      unfold f. field_simplify. 2 : { pose proof INR_fact_lt_0 n; lra. }
      admit.
  }
  assert (H6 : ∀ n, (n > 0)%nat -> 0 < ∫ 0 1 (λ x, π * a^n * f n x * sin (π * x)) < π * a^n / n!).
  {
    intros n H6. split.
    - apply integral_pos'; try lra. intros x H7. assert (x = 0 \/ x = 1 \/ (0 < x < 1)) as [H8 | [H8 | H8]] by solve_R.
      -- subst. rewrite Rmult_0_r. rewrite sin_0. lra.
      -- subst. rewrite Rmult_1_r. rewrite sin_π. lra.
      -- specialize (H5 n x H6 H8). lra.
      -- exists (1/2). split; solve_R. admit.
      -- admit.
      -- admit.
    - pose proof theorem_13_7 0 1 (λ x, π * a^n * f n x * sin (π * x)) 0 (π * a^n / n!) ltac:(lra).
      admit.
  }
  pose proof pow_over_factorial_tends_to_0 (a * π) (1) (ltac:(pose proof π_pos; nra)) (ltac:(lra)) as [n H7].
  specialize (H4 n) as [c H8].
  specialize (H6 n). pose proof π_pos as H9. assert (H10 : c > 0) by admit.
  assert (H11 : (a * π) ^ n >= π * a^n). { admit. }
  assert (H12 : π * (a^n) / n! < 1) by admit. 
Admitted.