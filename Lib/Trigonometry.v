From Lib Require Import Imports Notations Integral Derivative Functions Continuity Limit Sets Reals_util Inverse Interval Polynomial.
Import IntervalNotations SetNotations FunctionNotations DerivativeNotations LimitNotations.

Open Scope R_scope.

Definition π := 2 * ∫ (-1) 1 (λ x, √(1 - x^2)).

Lemma π_pos : π > 0.
Proof.
  set (f := λ x : R, √(1 - x ^ 2)).
  assert (H1 : ∀ x : ℝ, x ∈ [-1, 1] → 0 ≤ f x).
  { intros x H1. apply sqrt_pos. }
  assert (H2 : ∃ x : ℝ, x ∈ [-1, 1] ∧ f x > 0).
  { exists 0. split; solve_R. unfold f. apply sqrt_lt_R0. lra. }
  assert (H3 : continuous_on f [-1, 1]).
  {
    apply continuous_on_sqrt_comp. apply continuous_on_minus. 
    - apply continuous_on_const. 
    - apply continuous_on_pow; apply continuous_on_id.
  }
  pose proof integral_pos' (-1) 1 f ltac:(lra) H1 H2 H3 as H4.
  unfold π, f in *. lra.
Qed.

Definition A x :=
  match Rlt_dec x (-1) with
  | left _ => 0
  | right _ => match Rgt_dec x 1 with
               | left _ => 0
               | right _ => (x * √(1 - x^2) / 2) + ∫ x 1 (λ t, √(1 - t^2))
               end
  end.

Lemma A_spec : forall x, -1 <= x <= 1 -> A x = x * √(1 - x ^ 2) / 2 + ∫ x 1 (λ t, √(1 - t^2)).
Proof.
  intros x H1. unfold A. destruct (Rlt_dec x (-1)) as [H2 | H2]; try lra.
  destruct (Rgt_dec x 1) as [H3 | H3]; try lra.
Qed.

Lemma derivative_at_A : forall x, -1 < x < 1 ->
  ⟦ der x ⟧ A = (fun x => -1 / (2 * √(1 - x ^ 2))).
Proof.
  intros x H1.
  apply derivative_at_eq with (f1 := fun x => x * √(1 - x^2) / 2 + ∫ x 1 (λ t, √(1 - t^2))).
  - exists (Rmin (x - -1) (1 - x)). split; [ solve_R | ].
    intros y H2. rewrite A_spec; try lra. solve_R.
  - replace (λ x0, -1 / (2 * √(1 - x0^2))) with (λ x0, (1 - 2 * x0^2) / (2 * √(1 - x0^2)) - √(1 - x0^2)).
    2 : {
      extensionality y. assert (1 - y^2 <= 0 \/ 1 - y^2 > 0) as [H2 | H2] by lra.
      - rewrite sqrt_neg_0; auto. rewrite Rmult_0_r, Rdiv_0_r, Rdiv_0_r. lra.
      - assert (H3 : √(1 - y ^ 2) <> 0). { apply Rgt_not_eq. apply sqrt_lt_R0. auto. }
        field_simplify; auto. rewrite pow2_sqrt; try lra.
    }
    apply derivative_at_plus.
    + replace (λ x0 : ℝ, x0 * √(1 - x0 ^ 2) / 2) with (λ x0 : ℝ, 1/2 * (x0 * √(1 - x0 ^ 2))) by (extensionality y; lra).
    replace (λ x0 : ℝ, (1 - 2 * x0 ^ 2) / (2 * √(1 - x0 ^ 2))) with (λ x0 : ℝ, (1 / 2) * ((1 - 2 * x0 ^ 2) / √(1 - x0 ^ 2))).
    2 : { 
      extensionality y. assert (y^2 >= 1 \/ y^2 < 1) as [H2 | H2] by lra.
      - pose proof sqrt_neg_0 (1 - y^2) ltac:(lra) as H3.
        rewrite H3, Rmult_0_r, Rdiv_0_r, Rmult_0_r. lra.
      - solve_R. intros H3. pose proof sqrt_lt_R0 (1 - y^2) ltac:(lra) as H4. simpl in *. lra.
    }
      apply derivative_at_mult_const_l.
    set (f := (λ x0 : R, x0)). set (h := (λ x0, 1 - x0^2)). set (g := (λ x0 : R, √(h x0))).
     replace ((λ x0 : ℝ, x0 * √(1 - x0 ^ 2))) with (f ⋅ g).
    2 : { extensionality y. unfold f, g, h. lra. }
    set (f' := (λ x0 : R, 1)). assert ( ⟦ der x ⟧ f = f') as H2. { unfold f, f'. apply derivative_at_id. }
    set (h' := (λ x0, -2 * x0)). assert ( ⟦ der x ⟧ h = h') as H3.
    {
      unfold h, h'. replace ((λ x0, -2 * x0)) with (λ x0, 0 - (INR 2 * (x0^(2-1)))) by (extensionality y; solve_R).
      apply derivative_at_minus. apply derivative_at_const. apply derivative_at_pow.
    }
    set (g' := (λ x0, (h' x0) / (2 * √(h x0)))). assert ( ⟦ der x ⟧ g = g') as H4.
    { apply derivative_at_sqrt_comp; auto. unfold h. solve_R. }
    assert ( ⟦ der x ⟧ (f ⋅ g) = f' ⋅ g + f ⋅ g') as H5.
    { apply derivative_at_mult; auto. }
    replace (λ x0 : ℝ, (1 - 2 * x0 ^ 2) / √(1 - x0 ^ 2)) with (f' ⋅ g + f ⋅ g')%function; auto.
    extensionality y. assert (1 - y^2 <= 0 \/ 1 - y^2 > 0) as [H6 | H6] by lra.
    -- unfold f, g, f', g', h, h'. pose proof sqrt_neg_0 (1 - y^2) ltac:(lra) as H7.
       rewrite H7, Rmult_0_r, Rdiv_0_r, Rmult_0_r, Rdiv_0_r. lra.
    -- unfold f, g, f', g', h, h'.
     assert (H7 : √(1 - y^2) > 0).
    { apply sqrt_lt_R0. lra. }
    apply Rmult_eq_reg_r with (r := √(1 - y^2)); try lra. field_simplify; try lra.
    rewrite pow2_sqrt; try lra.
    + apply derivative_on_imp_derivative_at with (D := [-1, 1]); auto_interval.
      apply FTC1'; try lra. apply continuous_on_sqrt_comp. replace (λ x0 : ℝ, 1 - x0 * (x0 * 1)) with (polynomial [-1; 0; 1]).
      2 : { extensionality y. compute. lra. }
      apply continuous_on_polynomial.
Qed.

Lemma continuous_on_A : continuous_on A [-1, 1].
Proof.
  apply continuous_on_closed_interval_iff; try lra. repeat split.
  - intros x H1. apply differentiable_at_imp_continuous_at. 
    apply derivative_at_imp_differentiable_at with (f' := (fun x => -1 / (2 * √(1 - x ^ 2)))).
    apply derivative_at_A; solve_R.
  - unfold continuous_at_right. rewrite A_spec; try lra. apply limit_right_eq with (f1 := (fun x => x * √(1 - x ^ 2) / 2 + ∫ x 1 (λ t, √(1 - t^2)))); try lra.
    + exists 0.5. split; [lra |]. intros x H1. rewrite A_spec; solve_R.
    + apply limit_right_plus.
      * replace ((1 - (-1) ^ 2)) with 0 by lra. replace (-1 * √(0) / 2) with ((-1 / 2) * √(0)). 2 : { rewrite sqrt_0. lra. }
        apply limit_right_eq with (f1 := (λ x, (x / 2) * √(1 - x ^ 2))).
        { exists 1. split; [lra |]. intros x H1. lra. }
        apply limit_right_mult. 
        -- apply limit_right_mult. apply limit_right_id. apply limit_right_const.
        -- apply limit_right_sqrt_f_x; try lra. replace 0 with (1 - (-1)^2) by lra. apply limit_right_minus. apply limit_right_const. apply limit_right_pow. apply limit_right_id.
      * apply right_limit_integral_lower; solve_R. apply theorem_13_3; try lra.
        apply continuous_on_sqrt_comp. apply continuous_on_minus. apply continuous_on_const. repeat apply continuous_on_mult. apply continuous_on_id. apply continuous_on_id. apply continuous_on_const.
  - unfold continuous_at_left. rewrite A_spec; try lra. apply limit_left_eq with (f1 := (fun x => x * √(1 - x ^ 2) / 2 + ∫ x 1 (λ t, √(1 - t^2)))); try lra.
    + exists 0.5. split; [lra |]. intros x H1. rewrite A_spec; solve_R.
    + apply limit_left_plus.
      * replace ((1 - 1 ^ 2)) with 0 by lra. replace (1 * √(0) / 2) with ((1 / 2) * √(0)). 2 : { rewrite sqrt_0. lra. }
        apply limit_left_eq with (f1 := (λ x, (x / 2) * √(1 - x ^ 2))).
        { exists 1. split; [lra |]. intros x H1. lra. }
        apply limit_left_mult. 
        -- apply limit_left_mult. apply limit_left_id. apply limit_left_const.
        -- apply limit_left_sqrt_f_x; try lra. replace 0 with (1 - 1^2) by lra. apply limit_left_minus. apply limit_left_const. apply limit_left_pow. apply limit_left_id.
      * rewrite integral_n_n. apply left_limit_integral_at_upper_zero with (a := 0); solve_R.
        apply theorem_13_3; try lra.
        apply continuous_on_sqrt_comp. apply continuous_on_minus. apply continuous_on_const. repeat apply continuous_on_mult. apply continuous_on_id. apply continuous_on_id. apply continuous_on_const.
Qed.

Lemma A_at_1 : A 1 = 0.
Proof.
  rewrite A_spec; try lra. rewrite integral_n_n.
  replace (1 - 1 ^ 2) with 0 by lra. rewrite sqrt_0. lra.
Qed.

Lemma A_at_neg_1 : A (-1) = π / 2.
Proof.
  rewrite A_spec; try lra. replace ((1 - (-1) ^ 2)) with 0 by lra. rewrite sqrt_0. unfold π. lra.
Qed.

Lemma A_at_0 : A 0 = π / 4.
Proof.
  set (g := fun x => A x + A (-x)).
  assert (H1 : forall x, -1 < x < 1 -> ⟦ der x ⟧ g = (fun _ => 0)).
  {
    intros y H1.
    unfold g.
    replace (fun _ : ℝ => 0) with (fun x0 : ℝ => -1 / (2 * √(1 - x0^2)) + 1 / (2 * √(1 - x0^2))) by (extensionality z; lra).
    apply derivative_at_plus.
    - apply derivative_at_A; solve_R.
    - replace (fun x0 => A (- x0)) with (fun x0 => A (-1 * x0)) by (extensionality z; f_equal; lra).
      replace (fun x0 => 1 / (2 * √(1 - x0^2))) with (fun x0 => (-1 / (2 * √(1 - (-1 * x0)^2))) * -1).
      2 : { extensionality z. replace ((-1 * z) ^ 2) with (z ^ 2) by (field; lra). lra. }
      apply (derivative_at_comp (fun x0 => -1 * x0) A (fun _ => -1) (fun z => -1 / (2 * √(1 - z^2)))).
      + replace (λ _ : ℝ, -1) with (-1 * (λ _ : ℝ, 1))%function by (extensionality z; lra).
         apply derivative_at_mult_const_l. apply derivative_at_id.
      + apply derivative_at_A. solve_R.
  }
  assert (H2 : continuous_on g [-1, 1]).
  {
    unfold g. apply continuous_on_plus.
    - apply continuous_on_A.
    - replace (fun x => A (- x)) with (A ∘ (fun x => -1 * x)).
      2 : { extensionality z. unfold compose. f_equal. lra. }
      apply continuous_on_comp with (D2 := [-1, 1]).
      + apply continuous_on_mult_const_l. apply continuous_on_id.
      + intros x H2. solve_R.
      + apply continuous_on_A.
  }
  assert (H3 : g 0 = g 1).
  {
    pose proof MVT g (fun _ => 0) 0 1 ltac:(lra) as [c [H3 H4]].
    - apply continuous_on_subset with (A2 := [-1, 1]); auto.
      intros y Hy. solve_R.
    - apply derivative_at_imp_derivative_on.
      + apply differentiable_domain_open; lra.
      + intros y Hy. apply H1. solve_R.
    - lra.
  }
  unfold g in H3. replace (-(1)) with (-1) in H3 by lra.
  rewrite A_at_1, A_at_neg_1 in H3.
  replace (-0) with 0 in H3 by lra.
  lra.
Qed.

Lemma A_decreases : decreasing_on A [-1, 1].
Proof.
  apply derivative_on_neg_imp_decreasing_on_open with (f' := (fun x => -1 / (2 * √(1 - x ^ 2)))); try lra.
  - apply continuous_on_A.
  - apply derivative_at_imp_derivative_on.
    + apply differentiable_domain_open; lra.
    + apply derivative_at_A; auto.
  - intros x H1.
    apply Rdiv_neg_pos; try lra.
    apply Rmult_gt_0_compat; try lra.
    apply sqrt_lt_R0. solve_R.
Qed.

Lemma B_decreases : decreasing_on (2 * A) [-1, 1].
Proof.
  intros a b H1 H2 H3. specialize (A_decreases a b H1 H2 H3) as H4. lra.
Qed.

Theorem cos_existence_0 : 
  { y | y ∈ [-1, 1] /\ A y = 0 / 2 }.
Proof.
  exists 1. split; solve_R. rewrite A_at_1. lra.
Qed.

Theorem cos_existence_π : 
  { y | y ∈ [-1, 1] /\ A y = π / 2 }.
Proof.
  exists (-1). split; solve_R. rewrite A_at_neg_1. lra.
Qed.

Theorem cos_0_π_existence : forall x,
  0 <= x <= π -> { y | y ∈ [-1, 1] /\ A y = x / 2 }.
Proof.
  intros x H1.
  pose proof Req_dec_T x 0 as [H2 | H2].
  - subst. apply cos_existence_0.
  - pose proof Req_dec_T x π as [H3 | H3].
    -- subst. apply cos_existence_π.
    -- apply (intermediate_value_theorem_decreasing A (-1) 1); try lra; [ apply continuous_on_A | rewrite A_at_1, A_at_neg_1; lra ].
Qed.

Definition cos_0_π (x:R) : R :=
  match Rle_dec 0 x with
  | left H1 =>
    match Rle_dec x π with
    | left H2 =>
      proj1_sig (cos_0_π_existence x (conj H1 H2))
    | right _ => 0
    end
  | right _ => 0
  end.

Lemma cos_0_π_spec : forall x, 0 <= x <= π -> A (cos_0_π x) = x / 2.
Proof.
  intros x H1. unfold cos_0_π. destruct (Rle_dec 0 x) as [H2 | H2]; try lra.
  destruct (Rle_dec x π) as [H3 | H3]; try lra.
  pose proof (proj2_sig (cos_0_π_existence x (conj H2 H3))) as H4. lra.
Qed.

Lemma cos_0_π_in_range : forall x, 0 <= x <= π -> cos_0_π x ∈ [-1, 1].
Proof.
  intros x H1. unfold cos_0_π.
  destruct (Rle_dec 0 x) as [H2|H2]; destruct (Rle_dec x π) as [H3|H3]; try lra.
  pose proof (proj2_sig (cos_0_π_existence x (conj H2 H3))) as [H4 _]; auto.
Qed.

Definition sin_0_π (x:R) : R :=
  √(1 - (cos_0_π x) ^ 2).

Theorem theorem_15_1_a : forall x,
  0 < x < π -> ⟦ der x ⟧ cos_0_π = -sin_0_π.
Proof.
  intros x H1. set (B := fun x => 2 * A x).
  assert (H2 : B (cos_0_π x) = x).
  { unfold B. rewrite cos_0_π_spec; try lra. }
  pose proof derivative_at_A as H3.
  assert (∀ x, x ∈ (-1, 1) -> ⟦ der x ⟧ B = (λ x0, -1 / (√(1 - x0^2)))) as H4.
  {
    intros y H4. unfold B. replace (λ x0 : ℝ, -1 / √(1 - x0 ^ 2)) with (λ x0 : ℝ, 2 * (-1 / (2 * √(1 - x0 ^ 2)))).
    2 : { extensionality z. assert (√(1 - z ^ 2) = 0 \/ √(1 - z ^ 2) <> 0) as [H5 | H5] by lra.
          - rewrite H5. rewrite Rdiv_0_r, Rmult_0_r, Rdiv_0_r. lra.
          - field; auto.
    }
    apply derivative_at_mult_const_l. apply derivative_at_A; solve_R.
  }
  assert (H5 : -1 < 1) by lra.
  assert (H6 : continuous_on B [-1, 1]).
  {
    pose proof continuous_on_A as H6. unfold B. intros y H7. specialize (H6 y H7).
    apply limit_on_mult; auto. apply limit_on_const. 
  }
  assert (H7 : one_to_one_on B [-1, 1]).
  { apply decreasing_on_imp_one_to_one_on; try lra. apply B_decreases. }
  assert (H8 : inverse_on B cos_0_π [-1, 1] [0, π]).
  {
    assert (H8 : forall y, y  ∈ [-1, 1] -> B y ∈ [B 1, B (-1)]).
    {
      split; destruct (Req_dec_T y 1); destruct (Req_dec_T y (-1)); subst; try lra;
      apply Rlt_le; apply B_decreases; solve_R.
    }
    split; [| split; [| split]]; intros y H9.
    - specialize (H8 y H9). unfold B in *; rewrite A_at_1, A_at_neg_1 in *; solve_R.
    - apply cos_0_π_in_range; auto.
    - apply H7; auto.
      -- apply cos_0_π_in_range; auto.
        specialize (H8 y H9). unfold B in *; rewrite A_at_1, A_at_neg_1 in *; solve_R.
      -- unfold B. rewrite cos_0_π_spec; try lra.
        specialize (H8 y H9). unfold B in *; rewrite A_at_1, A_at_neg_1 in *; solve_R.
    - unfold B. rewrite cos_0_π_spec; auto. lra.
  }
  assert (H9 : x ∈ (Rmin (B (-1)) (B 1), Rmax (B (-1)) (B 1))).
  { unfold B. rewrite A_at_1, A_at_neg_1. solve_R. }
  assert (H10 : ⟦ der ⟧ B (-1, 1) = (λ x0, -1 / √(1 - x0 ^ 2))).
  { intros y H10. left; split. auto_interval. specialize (H4 y H10); auto. }
  assert (H11 : (λ x0, -1 / √(1 - x0 ^ 2)) (cos_0_π x) ≠ 0).
  {
    assert (H11: -1 < cos_0_π x < 1).
    {
      pose proof (cos_0_π_in_range x) as [H11 H12]; try lra.
      unfold B in H2. split.
      - destruct H11 as [H11 | H11]; auto. rewrite <- H11 in H2.
        rewrite A_at_neg_1 in H2. lra.
      - destruct H12 as [H12 | H12]; auto. rewrite H12 in H2.
        rewrite A_at_1 in H2. lra.
    }
    pose proof sqrt_lt_R0 (1 - cos_0_π x ^ 2) ltac:(solve_R) as H12.
    intros H13. pose proof Rdiv_neg_pos (-1) (√(1 - cos_0_π x ^ 2)) ltac:(lra) H12 as H14.
    lra.
  }
  assert (H12 : [0, π] = [Rmin (B (-1)) (B 1), Rmax (B (-1)) (B 1)]).
  {
    unfold B. rewrite A_at_1, A_at_neg_1, Rmin_right, Rmax_left by lra.
    rewrite Rmult_0_r. replace (2 * (π / 2)) with π by lra. reflexivity.
  }
  rewrite H12 in H8.
  pose proof (theorem_12_5 B cos_0_π (λ x0, -1 / √(1 - x0 ^ 2))
    (-1) 1 x H5 H6 H7 H8 H9 H10 H11) as H13.
  replace (- sin_0_π)%function with ( λ x : ℝ, / (λ x0 : ℝ, -1 / √(1 - x0 ^ 2)) (cos_0_π x)); auto.
  extensionality y. unfold sin_0_π. apply Rmult_eq_reg_r with (r := -1); try lra.
  assert (√(1 - cos_0_π y ^ 2) = 0 \/ √(1 - cos_0_π y ^ 2) <> 0) as [H14 | H14]; try lra.
  - rewrite H14, Rdiv_0_r, Rinv_0. lra.
  - solve_R.
Qed.

Lemma pythagorean_identity_0_π : forall x,
  0 <= x <= π -> (sin_0_π x)^2 + (cos_0_π x)^2 = 1.
Proof.
  intros x H1. unfold sin_0_π. assert (1 - cos_0_π x ^ 2 >= 0).
  { pose proof cos_0_π_in_range x H1; solve_R. }
  rewrite pow2_sqrt; lra.
Qed. 

Definition red_0_2π (x : ℝ) : { y : ℝ | 0 <= y < 2 * π /\ ∃ k : ℤ, x = y + IZR k * 2 * π }.
Proof.
  pose proof π_pos as H1.
  set (p := 2 * π).
  assert (H2: p > 0). { unfold p; lra. }
  remember (up (x / p)) as u eqn:H3.
  set (k := (u - 1)%Z).
  exists (x - IZR k * p).
  split.
  - destruct (archimed (x / p)) as [H4 H5].
    rewrite <- H3 in H4, H5. clear H3.
    unfold k. rewrite minus_IZR. split.
    + apply Rmult_le_reg_r with (r := / p).
      { apply Rinv_0_lt_compat; assumption. }
      rewrite Rmult_0_l.
      rewrite Rmult_minus_distr_r.
      rewrite Rmult_assoc. rewrite Rinv_r; [| lra]. lra. 
    + apply Rmult_lt_reg_r with (r := / p).
      { apply Rinv_0_lt_compat; assumption. }
      rewrite Rmult_minus_distr_r.
      rewrite Rmult_assoc. rewrite Rinv_r; lra.
  - exists k. unfold p. lra.
Qed.

Lemma red_0_2π_spec : ∀ x,
  let y := proj1_sig (red_0_2π x) in
  0 <= y < 2 * π /\ ∃ k : ℤ, x = y + IZR k * 2 * π.
Proof.
  intros x y. destruct (red_0_2π x) as [y0 [H1 H2]].
  simpl. split; auto.
Qed.

Definition cos_0_2π (y : ℝ) : ℝ :=
  if Rle_dec y π
  then cos_0_π y
  else cos_0_π (2 * π - y).

Definition cos (x : ℝ) : ℝ :=
  let y := proj1_sig (red_0_2π x) in cos_0_2π y.

Definition sin_0_2π (y : ℝ) : ℝ :=
  if Rle_dec y π
  then sin_0_π y
  else -sin_0_π (2 * π - y).

Definition sin (x : ℝ) : ℝ :=
  let y := proj1_sig (red_0_2π x) in sin_0_2π y.

Definition tan (x : ℝ) : ℝ :=
  sin x / cos x.

Definition sec (x : ℝ) : ℝ :=
  1 / cos x.

Definition csc (x : ℝ) : ℝ :=
  1 / sin x.

Definition cot (x : ℝ) : ℝ :=
  1 / tan x.

Lemma cos_on_0_π : ∀ x, 0 <= x <= π -> cos x = cos_0_π x.
Proof.
  intros x H1. unfold cos.
  destruct (red_0_2π_spec x) as [H2 [k H3]].
  set (y := proj1_sig (red_0_2π x)) in *.
  assert (H4: x = y).
  {
    assert (|(x - y)| < 2 * π) as H4 by solve_R.
    rewrite H3 in H4. 
    replace (y + IZR k * 2 * π - y) with (IZR k * 2 * π) in H4 by lra.
    assert (|(IZR k * 2 * π)| = (|(IZR k)| * 2 * π)) as H5 by solve_R.
    rewrite H5 in H4.
    destruct (Req_dec k 0) as [H6 | H6]; [solve_R | ].
    assert (|(IZR k)| >= 1).
    {
      assert ((k <= -1)%Z \/ (k = 0)%Z \/ (k >= 1)%Z) as [H7 | [H7 | H7]] by lia.
      - apply IZR_le in H7. solve_R.
      - rewrite H7 in *. lra. 
      - apply IZR_ge in H7. solve_R.
    }
    nra.
  }
  rewrite H4. unfold cos_0_2π.
  destruct (Rle_dec y π); try lra.
Qed.

Lemma cos_on_π_2π : ∀ x, π < x < 2 * π -> cos x = cos_0_π (2 * π - x).
Proof.
  intros x H1. unfold cos.
  destruct (red_0_2π_spec x) as [H2 [k H3]].
  set (y := proj1_sig (red_0_2π x)) in *.
  assert (H4: x = y).
  {
    assert (|(x - y)| < 2 * π) as H4 by solve_R.
    rewrite H3 in H4.
    replace (y + IZR k * 2 * π - y) with (IZR k * 2 * π) in H4 by lra.
    assert (|(IZR k * 2 * π)| = (|(IZR k)| * 2 * π)) as H5 by solve_R.
    rewrite H5 in H4.
    destruct (Z.eq_dec k 0) as [H6 | H6].
    - rewrite H6 in *. lra.
    - assert (|(IZR k)| >= 1) as H7. 
      {
        assert ((k <= -1)%Z \/ (k = 0)%Z \/ (k >= 1)%Z) as [H8 | [H8 | H8]] by lia.
        - apply IZR_le in H8. solve_R.
        - rewrite H8 in *. lia.
        - apply IZR_ge in H8. solve_R.
      }
      nra.
  }
  rewrite H4.
  unfold cos_0_2π. destruct (Rle_dec y π); lra.
Qed.

Lemma cos_periodic : ∀ x, cos (x + 2 * π) = cos x.
Proof.
  intros x. unfold cos.
  destruct (red_0_2π_spec x) as [H1 [k1 H2]].
  destruct (red_0_2π_spec (x + 2 * π)) as [H3 [k2 H4]].
  set (y1 := proj1_sig (red_0_2π x)) in *.
  set (y2 := proj1_sig (red_0_2π (x + 2 * π))) in *.
  assert (H5: y1 = y2).
  {
    assert (|(y1 - y2)| < 2 * π) as H5 by solve_R.
    rewrite H2 in H4.
    replace (y1 - y2) with ((IZR k2 - IZR k1 - 1) * 2 * π) in H5 by lra.
    set (k := (k2 - k1 - 1)%Z).
    replace (IZR k2 - IZR k1 - 1) with (IZR k) in H5.
    2:{ unfold k. repeat rewrite minus_IZR. simpl. reflexivity. }
    assert (|(IZR k * 2 * π)| = |(IZR k)| * 2 * π) as H6 by solve_R.
    rewrite H6 in H5.
    destruct (Z.eq_dec k 0) as [H7 | H7].
    - subst k. replace k2 with (k1 + 1)%Z in H4 by lia. rewrite plus_IZR in H4. lra.
    - assert (|(IZR k)| >= 1) as H8.
      {
        assert ((k <= -1)%Z \/ (k = 0)%Z \/ (k >= 1)%Z) as [H9 | [H9 | H9]] by lia.
        - apply IZR_le in H9. solve_R.
        - contradiction.
        - apply IZR_ge in H9. solve_R.
      }
      nra.
  }
  rewrite H5. reflexivity.
Qed.

Lemma cos_le_1 : ∀ x, cos x <= 1.
Proof.
  intros x.
  unfold cos.
  destruct (red_0_2π_spec x) as [H1 [k H2]].
  set (y := proj1_sig (red_0_2π x)) in *.
  unfold cos_0_2π.
  destruct (Rle_dec y π) as [H3 | H3].
  - pose proof cos_0_π_in_range y ltac:(lra) as [H4 H5].
    exact H5.
  - pose proof cos_0_π_in_range (2 * π - y) ltac:(lra) as [H4 H5].
    exact H5.
Qed.

Lemma cos_ge_neg1 : ∀ x, -1 <= cos x.
Proof.
  intros x.
  unfold cos.
  destruct (red_0_2π_spec x) as [H1 [k H2]].
  set (y := proj1_sig (red_0_2π x)) in *.
  unfold cos_0_2π.
  destruct (Rle_dec y π) as [H3 | H3].
  - pose proof cos_0_π_in_range y ltac:(lra) as [H4 H5].
    exact H4.
  - pose proof cos_0_π_in_range (2 * π - y) ltac:(lra) as [H4 H5].
    exact H4.
Qed.

Lemma A_inj : forall x y, x ∈ [-1, 1] -> y ∈ [-1, 1] -> A x = A y -> x = y.
Proof.
  intros x y H1 H2 H3.
  destruct (Rtotal_order x y) as [H4 | [H5 | H6]]; auto.
  - pose proof A_decreases x y H1 H2 H4 as H7. lra.
  - pose proof A_decreases y x H2 H1 H6 as H7. lra.
Qed.

Lemma cos_0 : cos 0 = 1.
Proof.
  pose proof π_pos as H1.
  assert (H2: 0 <= 0 <= π) by lra.
  rewrite cos_on_0_π; auto.
  apply A_inj.
  - apply cos_0_π_in_range; lra.
  - split; lra.
  - rewrite cos_0_π_spec; auto. rewrite A_at_1. lra.
Qed.

Lemma cos_π : cos π = -1.
Proof.
  pose proof π_pos as H1.
  assert (H2: 0 <= π <= π) by lra.
  rewrite cos_on_0_π; auto.
  apply A_inj.
  - apply cos_0_π_in_range; lra.
  - split; lra.
  - rewrite cos_0_π_spec; auto. rewrite A_at_neg_1. lra.
Qed.

Lemma cos_π_over_2 : cos (π / 2) = 0.
Proof.
  pose proof π_pos as H1.
  assert (H2: 0 <= π / 2 <= π) by lra.
  rewrite cos_on_0_π; auto.
  apply A_inj.
  - apply cos_0_π_in_range; lra.
  - split; lra.
  - rewrite cos_0_π_spec; auto. rewrite A_at_0. lra.
Qed.

Lemma sin_consistency_on_0_π : ∀ x, 0 <= x <= π -> sin x = sin_0_π x.
Proof.
  intros x H1.
  unfold sin.
  destruct (red_0_2π_spec x) as [H2 [k H3]].
  set (y := proj1_sig (red_0_2π x)) in *.
  assert (H4: x = y).
  {
    assert (|(x - y)| < 2 * π) as H4 by solve_R.
    rewrite H3 in H4.
    replace (y + IZR k * 2 * π - y) with (IZR k * 2 * π) in H4 by lra.
    assert (|(IZR k * 2 * π)| = (|(IZR k)| * 2 * π)) as H5 by solve_R.
    rewrite H5 in H4.
    destruct (Z.eq_dec k 0) as [H6 | H6].
    - rewrite H6 in *. lra.
    - assert (|(IZR k)| >= 1) as H7. 
      {
        assert ((k <= -1)%Z \/ (k = 0)%Z \/ (k >= 1)%Z) as [H8 | [H8 | H8]] by lia.
        - apply IZR_le in H8. solve_R.
        - rewrite H8 in *. lia.
        - apply IZR_ge in H8. solve_R.
      }
      pose proof π_pos as H8. nra.
  }
  rewrite H4. unfold sin_0_2π.
  destruct (Rle_dec y π); try lra.
Qed.

Lemma sin_periodic : ∀ x, sin (x + 2 * π) = sin x.
Proof.
  intros x. unfold sin. 
  destruct (red_0_2π_spec x) as [H1 [k1 H2]].
  destruct (red_0_2π_spec (x + 2 * π)) as [H3 [k2 H4]].
  set (y1 := proj1_sig (red_0_2π x)) in *.
  set (y2 := proj1_sig (red_0_2π (x + 2 * π))) in *.
  assert (H5: y1 = y2).
  {
    assert (|(y1 - y2)| < 2 * π) as H5 by solve_R.
    rewrite H2 in H4.
    replace (y1 - y2) with ((IZR k2 - IZR k1 - 1) * 2 * π) in H5 by lra.
    set (k := (k2 - k1 - 1)%Z).
    replace (IZR k2 - IZR k1 - 1) with (IZR k) in H5.
    2:{ unfold k. repeat rewrite minus_IZR. simpl. reflexivity. }
    assert (|(IZR k * 2 * π)| = |(IZR k)| * 2 * π) as H6 by solve_R.
    rewrite H6 in H5.
    destruct (Z.eq_dec k 0) as [H7 | H7].
    - subst k. replace k2 with (k1 + 1)%Z in H4 by lia. rewrite plus_IZR in H4. lra.
    - assert (|(IZR k)| >= 1) as H8.
      {
        assert ((k <= -1)%Z \/ (k = 0)%Z \/ (k >= 1)%Z) as [H9 | [H9 | H9]] by lia.
        - apply IZR_le in H9. solve_R.
        - contradiction.
        - apply IZR_ge in H9. solve_R.
      }
      nra.
  }
  rewrite H5. reflexivity.
Qed.

Lemma continuous_on_cos_0_π : continuous_on cos_0_π [0, π].
Proof.
  set (B := fun x => 2 * A x).
  assert (H1 : -1 < 1) by lra.
  assert (H2 : continuous_on B [-1, 1]).
  {
    pose proof continuous_on_A as H2a. unfold B. intros y H2b. specialize (H2a y H2b).
    apply limit_on_mult; auto. apply limit_on_const. 
  }
  assert (H3 : one_to_one_on B [-1, 1]).
  { 
    apply decreasing_on_imp_one_to_one_on; try lra. apply B_decreases.
  }
  assert (H4 : inverse_on B cos_0_π [-1, 1] [0, π]).
  {
    assert (H4a : forall y, y ∈ [-1, 1] -> B y ∈ [B 1, B (-1)]).
    {
      intros y H4b. split; destruct (Req_dec_T y 1); destruct (Req_dec_T y (-1)); subst; try lra;
      apply Rlt_le; apply B_decreases; solve_R.
    }
    split; [| split; [| split]]; intros y H4b.
    - specialize (H4a y H4b).
      unfold B in *; rewrite A_at_1, A_at_neg_1 in *; solve_R.
    - apply cos_0_π_in_range; auto.
    - apply H3; auto.
      + apply cos_0_π_in_range; auto.
        specialize (H4a y H4b). unfold B in *; rewrite A_at_1, A_at_neg_1 in *; solve_R.
      + unfold B. rewrite cos_0_π_spec; try lra.
        specialize (H4a y H4b). unfold B in *; rewrite A_at_1, A_at_neg_1 in *; solve_R.
    - unfold B. rewrite cos_0_π_spec; auto. lra.
  }
  assert (H5 : [0, π] = [Rmin (B (-1)) (B 1), Rmax (B (-1)) (B 1)]).
  {
    unfold B. rewrite A_at_1, A_at_neg_1, Rmult_0_r. replace (2 * (π / 2)) with π by lra.
    pose proof π_pos as H6. solve_R.
  }
  rewrite H5. rewrite H5 in H4.
  eapply theorem_12_3; eauto.
Qed.

Lemma continuous_at_cos_0 : continuous_at cos 0.
Proof.
  unfold continuous_at. rewrite cos_0.
  apply limit_iff. split.
  - apply limit_left_eq with (f1 := fun x => cos_0_π (- x)).
    + exists π. split; [pose proof π_pos; lra |].
      intros x H1.
      replace x with (x + 2 * π - 2 * π) at 1 by lra.
      rewrite <- cos_periodic.
      rewrite cos_on_π_2π; [| lra].
      f_equal. lra.
    + assert (H1 : continuous_on (λ x, cos_0_π (- x)) [-π, 0]).
      {
        apply continuous_on_eq with (f1 := fun x => cos_0_π (-1 * x)).
        - intros y H2. f_equal; lra.
        - eapply continuous_on_comp with (f := cos_0_π) (g := fun x => -1 * x) (D2 := [0, π]).
          + apply continuous_on_mult_const_l. apply continuous_on_id.
          + intros y H2. pose proof π_pos as H3. solve_R.
          + apply continuous_on_cos_0_π.
      }
      pose proof π_pos as H2. specialize (H1 0 ltac:(solve_R)).
      assert (H3 : (λ x : ℝ, cos_0_π (- x)) 0 = 1).
      { simpl. replace (-0) with 0 by lra. rewrite <- cos_on_0_π; [apply cos_0 | solve_R]. }
      intros ε H4.
      destruct (H1 ε H4) as [δ [H5 H6]].
      exists (Rmin δ π). split; [solve_R | ].
      intros x H7.
      specialize (H6 x ltac:(solve_R) ltac:(solve_R)). solve_R.
  - apply limit_right_eq with (f1 := cos_0_π).
    + exists π. split; [pose proof π_pos; lra |].
      intros x H1. symmetry. apply cos_on_0_π. solve_R.
    + pose proof continuous_on_cos_0_π as H1.
      pose proof π_pos as H2. specialize (H1 0 ltac:(solve_R)).
      assert (H3 : cos_0_π 0 = 1).
      { rewrite <- cos_on_0_π; [apply cos_0 | solve_R]. }
      rewrite H3 in H1.
      intros ε H4.
      destruct (H1 ε H4) as [δ [H5 H6]].
      exists (Rmin δ π). split; [solve_R |].
      intros x H7.
      specialize (H6 x ltac:(solve_R) ltac:(solve_R)). solve_R.
Qed.

Lemma continuous_at_cos_π : continuous_at cos π.
Proof.
  unfold continuous_at. rewrite cos_π.
  apply limit_iff. split.
  - apply limit_left_eq with (f1 := cos_0_π).
    + exists π. split; [pose proof π_pos; lra |].
      intros x H1. symmetry. apply cos_on_0_π. solve_R.
    + pose proof continuous_on_cos_0_π as H1.
      pose proof π_pos as H2. specialize (H1 π ltac:(solve_R)).
      assert (H3 : cos_0_π π = -1).
      { rewrite <- cos_on_0_π; [apply cos_π | solve_R]. }
      rewrite H3 in H1.
      intros ε H4.
      destruct (H1 ε H4) as [δ [H5 H6]].
      exists (Rmin δ π). split; [solve_R |].
      intros x H7.
      specialize (H6 x ltac:(solve_R) ltac:(solve_R)). solve_R.
  - apply limit_right_eq with (f1 := fun x => cos_0_π (2 * π - x)).
    + exists π. split; [pose proof π_pos; lra |].
      intros x H1. symmetry. apply cos_on_π_2π. solve_R.
    + assert (H1 : continuous_on (λ x, cos_0_π (2 * π - x)) [π, 2 * π]).
      {
        eapply continuous_on_comp with (f := cos_0_π) (g := fun x => 2 * π - x) (D2 := [0, π]).
        - apply continuous_on_minus; [apply continuous_on_const | apply continuous_on_id].
        - intros y H2. pose proof π_pos as H3. solve_R.
        - apply continuous_on_cos_0_π.
      }
      pose proof π_pos as H2. specialize (H1 π ltac:(solve_R)).
      assert (H3 : (λ x : ℝ, cos_0_π (2 * π - x)) π = -1).
      { simpl. replace (2 * π - π) with π by lra. rewrite <- cos_on_0_π; [apply cos_π | solve_R]. }
      intros ε H4.
      destruct (H1 ε H4) as [δ [H5 H6]].
      exists (Rmin δ π). split; [solve_R |].
      intros x H7.
      specialize (H6 x ltac:(solve_R) ltac:(solve_R)). solve_R.
Qed.

Lemma continuous_on_sin_0_π : continuous_on sin_0_π [0, π].
Proof.
  unfold sin_0_π.
  apply continuous_on_sqrt_comp.
  apply continuous_on_minus; [apply continuous_on_const |].
  apply continuous_on_eq with (f1 := fun x => cos_0_π x * cos_0_π x).
  - intros x H1. lra.
  - apply continuous_on_mult; apply continuous_on_cos_0_π.
Qed.

Lemma limit_sin_0 : ⟦ lim 0 ⟧ sin = 0.
Proof.
  apply limit_iff. split.
  - apply limit_left_eq with (f1 := fun x => - sin_0_π (-x)).
    + exists π. split; [pose proof π_pos; lra |].
      intros x H1.
      replace x with (x + 2 * π - 2 * π) at 1 by lra.
      rewrite <- sin_periodic.
      unfold sin. destruct (red_0_2π_spec (x + 2 * π)) as [H2 [k H3]].
      set (y := proj1_sig (red_0_2π (x + 2 * π))) in *.
      assert (H4 : x + 2 * π = y).
      {
        assert (|(x + 2 * π - y)| < 2 * π) as H4 by solve_R.
        rewrite H3 in H4.
        replace (y + IZR k * 2 * π - y) with (IZR k * 2 * π) in H4 by lra.
        assert (|(IZR k * 2 * π)| = |(IZR k)| * 2 * π) as H5 by solve_R.
        rewrite H5 in H4. destruct (Z.eq_dec k 0) as [H6 | H6].
        - rewrite H6 in *. lra.
        - assert (|(IZR k)| >= 1) as H7.
          { assert ((k <= -1)%Z \/ (k = 0)%Z \/ (k >= 1)%Z) as [H8 | [H8 | H8]] by lia.
            - apply IZR_le in H8. solve_R.
            - lia.
            - apply IZR_ge in H8. solve_R. }
          pose proof π_pos as H8. nra.
      }
      rewrite H4. unfold sin_0_2π.
      destruct (Rle_dec y π) as [H5 | H5].
      * pose proof π_pos as H6. nra.
      * f_equal. f_equal. lra.
    + pose proof continuous_on_sin_0_π as H1.
      pose proof π_pos as H2. specialize (H1 0 ltac:(solve_R)).
      assert (H3 : sin_0_π 0 = 0).
      { unfold sin_0_π. rewrite <- cos_on_0_π; try lra. rewrite cos_0. replace (1 - 1 ^ 2) with 0 by lra. apply sqrt_0. }
      rewrite H3 in H1.
      intros ε H4. destruct (H1 ε H4) as [δ [H5 H6]].
      exists (Rmin δ π). split; [solve_R |].
      intros x H7.
      specialize (H6 (-x) ltac:(solve_R) ltac:(solve_R)).
      solve_R.
  - apply limit_right_eq with (f1 := sin_0_π).
    + exists π. split; [pose proof π_pos; lra |].
      intros x H1. symmetry. apply sin_consistency_on_0_π. solve_R.
    + pose proof continuous_on_sin_0_π as H1.
      pose proof π_pos as H2. specialize (H1 0 ltac:(solve_R)).
      assert (H3 : sin_0_π 0 = 0).
      { unfold sin_0_π. rewrite <- cos_on_0_π; try lra. rewrite cos_0. replace (1 - 1 ^ 2) with 0 by lra. apply sqrt_0. }
      rewrite H3 in H1.
      intros ε H4. destruct (H1 ε H4) as [δ [H5 H6]].
      exists (Rmin δ π). split; [solve_R |].
      intros x H7. specialize (H6 x ltac:(solve_R) ltac:(solve_R)). solve_R.
Qed.

Lemma limit_sin_π : ⟦ lim π ⟧ sin = 0.
Proof.
  apply limit_iff. split.
  - apply limit_left_eq with (f1 := sin_0_π).
    + exists π. split; [pose proof π_pos; lra |].
      intros x H1. symmetry. apply sin_consistency_on_0_π. solve_R.
    + pose proof continuous_on_sin_0_π as H1.
      pose proof π_pos as H2. specialize (H1 π ltac:(solve_R)).
      assert (H3 : sin_0_π π = 0).
      { unfold sin_0_π. rewrite <- cos_on_0_π; try lra. rewrite cos_π. replace (1 - (-1) ^ 2) with 0 by lra. apply sqrt_0. }
      rewrite H3 in H1.
      intros ε H4. destruct (H1 ε H4) as [δ [H5 H6]].
      exists (Rmin δ π). split; [solve_R |].
      intros x H7. specialize (H6 x ltac:(solve_R) ltac:(solve_R)). solve_R.
  - apply limit_right_eq with (f1 := fun x => - sin_0_π (2 * π - x)).
    + exists π. split; [pose proof π_pos; lra |].
      intros x H1.
      unfold sin. destruct (red_0_2π_spec x) as [H2 [k H3]].
      set (y := proj1_sig (red_0_2π x)) in *.
      assert (H4 : x = y).
      {
        assert (|(x - y)| < 2 * π) as H4 by solve_R.
        rewrite H3 in H4.
        replace (y + IZR k * 2 * π - y) with (IZR k * 2 * π) in H4 by lra.
        assert (|(IZR k * 2 * π)| = |(IZR k)| * 2 * π) as H5 by solve_R.
        rewrite H5 in H4. destruct (Z.eq_dec k 0) as [H6 | H6].
        - rewrite H6 in *. lra.
        - assert (|(IZR k)| >= 1) as H7.
          { assert ((k <= -1)%Z \/ (k = 0)%Z \/ (k >= 1)%Z) as [H8 | [H8 | H8]] by lia.
            - apply IZR_le in H8. solve_R.
            - lia.
            - apply IZR_ge in H8. solve_R. }
          pose proof π_pos as H8. nra.
      }
      rewrite H4. unfold sin_0_2π.
      destruct (Rle_dec y π) as [H5 | H5].
      * pose proof π_pos as H6. nra.
      * reflexivity.
    + pose proof continuous_on_sin_0_π as H1.
      pose proof π_pos as H2. specialize (H1 π ltac:(solve_R)).
      assert (H3 : sin_0_π π = 0).
      { unfold sin_0_π. rewrite <- cos_on_0_π; try lra. rewrite cos_π. replace (1 - (-1) ^ 2) with 0 by lra. apply sqrt_0. }
      rewrite H3 in H1.
      intros ε H4. destruct (H1 ε H4) as [δ [H5 H6]].
      exists (Rmin δ π). split; [solve_R |].
      intros x H7.
      specialize (H6 (2 * π - x) ltac:(solve_R) ltac:(solve_R)).
      solve_R.
Qed.

Lemma sin_0 : sin 0 = 0.
Proof.
  pose proof π_pos as H1.
  assert (H2: 0 <= 0 <= π) by lra.
  rewrite sin_consistency_on_0_π; auto.
  unfold sin_0_π.
  assert (H3 : cos_0_π 0 = 1).
  { rewrite <- cos_on_0_π; auto. apply cos_0. }
  rewrite H3. replace (1 - 1 ^ 2) with 0 by lra. apply sqrt_0.
Qed.

Lemma sin_π : sin π = 0.
Proof.
  pose proof π_pos as H1.
  assert (H2: 0 <= π <= π) by lra.
  rewrite sin_consistency_on_0_π; auto.
  unfold sin_0_π.
  assert (H3 : cos_0_π π = -1).
  { rewrite <- cos_on_0_π; auto. apply cos_π. }
  rewrite H3. replace (1 - (-1) ^ 2) with 0 by lra. apply sqrt_0.
Qed.

Lemma derivative_at_cos : forall x, ⟦ der x ⟧ cos = - sin.
Proof.
  intros x.
  assert (H1 : forall y, 0 < y < π -> ⟦ der y ⟧ cos = - sin).
  {
    intros y H1.
    apply derivative_at_ext_val with (f' := (- sin_0_π)%function).
    - apply derivative_at_eq with (f1 := cos_0_π).
      + exists (Rmin y (π - y)). split.
        * pose proof π_pos. apply Rmin_pos; lra.
        * intros z Hz. symmetry. apply cos_on_0_π. pose proof π_pos; solve_R.
      + apply theorem_15_1_a; auto.
    - pose proof (sin_consistency_on_0_π y) as H2.
      assert (0 <= y <= π) by lra.
      specialize (H2 H). lra.
  }
  assert (H2 : forall y, π < y < 2 * π -> ⟦ der y ⟧ cos = - sin).
  {
    intros y H2.
    apply derivative_at_eq with (f1 := fun z => cos_0_π (2 * π - z)).
    - exists (Rmin (y - π) (2 * π - y)). split.
      + pose proof π_pos. apply Rmin_pos; lra.
      + intros z Hz. symmetry. apply cos_on_π_2π. pose proof π_pos; solve_R.
    - eapply derivative_at_ext_val.
      + apply derivative_at_comp with (f := fun z => 2 * π - z) (g := cos_0_π).
        * apply derivative_at_minus; [apply derivative_at_const | apply derivative_at_id].
        * apply theorem_15_1_a. pose proof π_pos; solve_R.
      + unfold compose.
        unfold sin.
        destruct (red_0_2π_spec y) as [H3 [k H4]].
        set (y0 := proj1_sig (red_0_2π y)) in *.
        assert (H5 : y = y0).
        { assert (|(y - y0)| < 2 * π) as H5 by solve_R.
          rewrite H4 in H5.
          replace (y0 + IZR k * 2 * π - y0) with (IZR k * 2 * π) in H5 by lra.
          assert (|(IZR k * 2 * π)| = (|(IZR k)| * 2 * π)) as H6 by solve_R.
          rewrite H6 in H5. destruct (Z.eq_dec k 0) as [H7 | H7].
          - rewrite H7 in *. lra.
          - assert (|(IZR k)| >= 1) as H8.
            { assert ((k <= -1)%Z \/ (k = 0)%Z \/ (k >= 1)%Z) as [H9 | [H9 | H9]] by lia.
              - apply IZR_le in H9. solve_R.
              - lia.
              - apply IZR_ge in H9. solve_R. }
            pose proof π_pos. nra. }
        rewrite <- H5. unfold sin_0_2π. destruct (Rle_dec y π) as [H6 | H6]; try lra.
  }
  assert (H3 : forall y, ⟦ der y ⟧ cos = - sin -> ⟦ der (y + 2 * π) ⟧ cos = - sin).
  {
    intros y H3.
    apply derivative_at_eq with (f1 := fun z => cos (z - 2 * π)).
    - exists 1. split; [lra |]. intros z H4. rewrite <- cos_periodic.
      replace (z - 2 * π + 2 * π) with z by lra. reflexivity.
    - eapply derivative_at_ext_val.
      + apply derivative_at_comp with (f := fun z => z - 2 * π) (g := cos).
        * apply derivative_at_minus; [apply derivative_at_id | apply derivative_at_const].
        * replace (y + 2 * π - 2 * π) with y by lra. exact H3.
      + unfold compose.
        replace (y + 2 * π - 2 * π) with y by lra.
        pose proof (sin_periodic y).
        replace (y + 2 * π) with (y + 2 * π) in H by lra.
        lra.
  }
  assert (H4 : forall y, ⟦ der (y + 2 * π) ⟧ cos = - sin -> ⟦ der y ⟧ cos = - sin).
  {
    intros y H4.
    apply derivative_at_eq with (f1 := fun z => cos (z + 2 * π)).
    - exists 1. split; [lra |]. intros z H5. apply cos_periodic.
    - eapply derivative_at_ext_val.
      + apply derivative_at_comp with (f := fun z => z + 2 * π) (g := cos).
        * apply derivative_at_plus; [apply derivative_at_id | apply derivative_at_const].
        * exact H4.
      + unfold compose. pose proof (sin_periodic y) as H5. lra.
  }
  assert (H5 : ⟦ der 0 ⟧ cos = - sin).
  {
    eapply derivative_at_ext_val.
    - apply limit_derivative_imp_derivative_at with (f' := (- sin)%function).
      + apply continuous_at_cos_0.
      + exists π. split; [pose proof π_pos; lra |].
        intros y H5 H6.
        assert (0 < y < π \/ -π < y < 0) as [H7 | H7] by solve_R.
        * apply H1; auto.
        * apply H4. apply H2. pose proof π_pos; lra.
      + apply limit_eq with (f1 := fun x => -1 * sin x).
        * exists 1. split; [lra |]. intros y H5. lra.
        * replace 0 with (-1 * sin 0) at 2 by (rewrite sin_0; lra).
          apply limit_mult. apply limit_const. apply limit_sin_0.
    - simpl. rewrite sin_0. rewrite Rmult_0_r. lra.
  }
  assert (H6 : ⟦ der π ⟧ cos = - sin).
  {
    eapply derivative_at_ext_val.
    - apply limit_derivative_imp_derivative_at with (f' := (- sin)%function).
      + apply continuous_at_cos_π.
      + exists π. split; [pose proof π_pos; lra |].
        intros y H6 H7.
        assert (0 < y < π \/ π < y < 2 * π) as [H8 | H8] by solve_R.
        * apply H1; auto.
        * apply H2; auto.
      + apply limit_eq with (f1 := fun x => -1 * sin x).
        * exists 1. split; [lra |]. intros y H6. lra.
        * replace 0 with (-1 * sin π) at 2 by (rewrite sin_π; lra).
          apply limit_mult; [apply limit_const | apply limit_sin_π ].
    - simpl. rewrite sin_π. rewrite Rmult_0_r. lra.
  }
  destruct (red_0_2π_spec x) as [H7 [k H8]].
  set (y := proj1_sig (red_0_2π x)) in *.
  assert (H9 : ⟦ der y ⟧ cos = - sin).
  {
    assert (y = 0 \/ 0 < y < π \/ y = π \/ π < y < 2 * π) as [H9 | [H9 | [H9 | H9]]] by solve_R.
    - subst y. rewrite H9. auto.
    - apply H1; auto.
    - subst y. rewrite H9. auto.
    - apply H2; auto.
  }
  apply derivative_at_eq with (f1 := fun z => cos (z - IZR k * 2 * π)).
  - exists 1. split; [lra |]. intros z H10.
    unfold cos.
    destruct (red_0_2π_spec z) as [H11 [k1 H12]].
    destruct (red_0_2π_spec (z - IZR k * 2 * π)) as [H13 [k2 H14]].
    set (z1 := proj1_sig (red_0_2π z)) in *.
    set (z2 := proj1_sig (red_0_2π (z - IZR k * 2 * π))) in *.
    assert (H15 : z1 = z2).
    {
      assert (|(z1 - z2)| < 2 * π) as H15 by solve_R.
      rewrite H12 in H14.
      replace (z1 - z2) with ((IZR k2 - IZR k1 + IZR k) * 2 * π) in H15 by lra.
      set (m := (k2 - k1 + k)%Z).
      replace (IZR k2 - IZR k1 + IZR k) with (IZR m) in H15.
      2: { unfold m. repeat rewrite plus_IZR; repeat rewrite minus_IZR; lra. }
      assert (|(IZR m * 2 * π)| = |(IZR m)| * 2 * π) as H16 by solve_R.
      rewrite H16 in H15.
      destruct (Z.eq_dec m 0) as [H17 | H17].
      - assert (k2 = (k1 - k)%Z) as H18 by lia.
        rewrite H18 in H14.
        rewrite minus_IZR in H14.
        lra.
      - assert (|(IZR m)| >= 1) as H18.
        { assert ((m <= -1)%Z \/ (m = 0)%Z \/ (m >= 1)%Z) as [H19 | [H19 | H19]] by lia.
          - apply IZR_le in H19. solve_R.
          - lia.
          - apply IZR_ge in H19. solve_R. }
        pose proof π_pos as H19. nra.
    }
    rewrite H15. reflexivity.
  - eapply derivative_at_ext_val.
    + apply derivative_at_comp with (f := fun z => z - IZR k * 2 * π) (g := cos).
      * apply derivative_at_minus; [apply derivative_at_id | apply derivative_at_const].
      * replace (x - IZR k * 2 * π) with y by lra. exact H9.
    + unfold compose. replace (x - IZR k * 2 * π) with y by lra.
      unfold sin.
      destruct (red_0_2π_spec x) as [H10 [k1 H11]].
      destruct (red_0_2π_spec y) as [H12 [k2 H13]].
      set (y1 := proj1_sig (red_0_2π x)) in *.
      set (y2 := proj1_sig (red_0_2π y)) in *.
      assert (H14 : y1 = y2).
      {
        assert (|(y1 - y2)| < 2 * π) as H14 by solve_R.
        rewrite H8 in H11. rewrite H13 in H11.
        replace (y1 - y2) with ((IZR k2 - IZR k1 + IZR k) * 2 * π) in H14 by lra.
        set (m := (k2 - k1 + k)%Z).
        replace (IZR k2 - IZR k1 + IZR k) with (IZR m) in H14.
        2: { unfold m. repeat rewrite plus_IZR; repeat rewrite minus_IZR; lra. }
        assert (|(IZR m * 2 * π)| = |(IZR m)| * 2 * π) as H15 by solve_R.
        rewrite H15 in H14.
        destruct (Z.eq_dec m 0) as [H16 | H16].
        - assert (k1 = (k2 + k)%Z) as H17 by lia.
          rewrite H17 in H11.
          rewrite plus_IZR in H11.
          lra.
        - assert (|(IZR m)| >= 1) as H17.
          { assert ((m <= -1)%Z \/ (m = 0)%Z \/ (m >= 1)%Z) as [H18 | [H18 | H18]] by lia.
            - apply IZR_le in H18. solve_R.
            - lia.
            - apply IZR_ge in H18. solve_R. }
          pose proof π_pos as H18. nra.
      }
      rewrite H14. lra.
Qed.

Lemma derivative_cos :
  ⟦ der ⟧ cos = -sin.
Proof.
  intros x.
  apply derivative_at_cos.
Qed.


Lemma differentiable_cos : differentiable cos.
Proof.
  intros x.
  apply derivative_at_imp_differentiable_at with (f' := fun x => - sin x).
  apply derivative_at_cos.
Qed.

Lemma continuous_cos : continuous cos.
Proof.
  apply differentiable_imp_continuous.
  apply differentiable_cos.
Qed.

Lemma left_limit_cos : forall a,
  ⟦ lim a⁻ ⟧ cos = cos a.
Proof. intros a. apply continuous_at_imp_left_continuous. apply continuous_cos. Qed.

Lemma right_limit_cos : forall a,
  ⟦ lim a⁺ ⟧ cos = cos a.
Proof. intros a. apply continuous_at_imp_right_continuous. apply continuous_cos. Qed.

Lemma limit_cos : forall a,
  ⟦ lim a ⟧ cos = cos a.
Proof.
  intros a.
  apply limit_iff; split; [ apply left_limit_cos | apply right_limit_cos ].
Qed.

Lemma derivative_at_sin : forall x, ⟦ der x ⟧ sin = cos.
Proof.
  intros x.
  assert (H1 : forall y, 0 < y < π -> ⟦ der y ⟧ sin_0_π = cos_0_π).
  {
    intros y H2. unfold sin_0_π. eapply derivative_at_ext_val.
    - apply derivative_at_sqrt_comp.
      + assert (H3 : cos_0_π y ∈ [-1, 1]) by (apply cos_0_π_in_range; lra).
        assert (H4 : cos_0_π y <> 1). { intro H5. pose proof cos_0_π_spec y ltac:(lra) as H6. rewrite H5 in H6. rewrite A_at_1 in H6. lra. }
        assert (H5 : cos_0_π y <> -1). { intro H6. pose proof cos_0_π_spec y ltac:(lra) as H7. rewrite H6 in H7. rewrite A_at_neg_1 in H7. pose proof π_pos. lra. }
        destruct H3 as [H3a H3b]. nra.
      + replace (fun z => 1 - cos_0_π z ^ 2) with (fun z => 1 - cos_0_π z * cos_0_π z) by (extensionality z; lra).
        apply derivative_at_minus; [apply derivative_at_const |].
        apply derivative_at_mult; apply theorem_15_1_a; auto.
    - simpl.
      assert (H3 : cos_0_π y ∈ [-1, 1]) by (apply cos_0_π_in_range; lra).
      assert (H4 : cos_0_π y <> 1). { intro H5. pose proof cos_0_π_spec y ltac:(lra) as H6. rewrite H5 in H6. rewrite A_at_1 in H6. lra. }
      assert (H5 : cos_0_π y <> -1). { intro H6. pose proof cos_0_π_spec y ltac:(lra) as H7. rewrite H6 in H7. rewrite A_at_neg_1 in H7. pose proof π_pos. lra. }
      assert (H6 : √(1 - cos_0_π y ^ 2) > 0). { apply sqrt_lt_R0. destruct H3 as [H3a H3b]. nra. }
      unfold sin_0_π.
      replace (1 - cos_0_π y * (cos_0_π y * 1)) with (1 - cos_0_π y ^ 2) by lra.
      field. lra.
  }
  assert (H2 : forall y, 0 < y < π -> ⟦ der y ⟧ sin = cos).
  {
    intros y H3.
    apply derivative_at_ext_val with (f' := cos_0_π).
    - apply derivative_at_eq with (f1 := sin_0_π).
      + exists (Rmin y (π - y)). split.
        * pose proof π_pos as H4. apply Rmin_pos; lra.
        * intros z H4. symmetry. apply sin_consistency_on_0_π. pose proof π_pos as H5; solve_R.
      + apply H1; auto.
    - pose proof (cos_on_0_π y) as H4. assert (0 <= y <= π) as H5 by lra. specialize (H4 H5). lra.
  }
  assert (H3 : forall y, π < y < 2 * π -> ⟦ der y ⟧ sin = cos).
  {
    intros y H4.
    apply derivative_at_eq with (f1 := fun z => - sin_0_π (2 * π - z)).
    - exists (Rmin (y - π) (2 * π - y)). split.
      + pose proof π_pos as H5. apply Rmin_pos; lra.
      + intros z H5. unfold sin.
        destruct (red_0_2π_spec z) as [H6 [k H7]].
        set (z0 := proj1_sig (red_0_2π z)) in *.
        assert (H8 : z = z0).
        {
          assert (|(z - z0)| < 2 * π) as H9 by solve_R.
          rewrite H7 in H9. replace (z0 + IZR k * 2 * π - z0) with (IZR k * 2 * π) in H9 by lra.
          assert (|(IZR k * 2 * π)| = (|(IZR k)| * 2 * π)) as H10 by solve_R. rewrite H10 in H9.
          destruct (Z.eq_dec k 0) as [H11 | H11].
          - rewrite H11 in *. lra.
          - assert (|(IZR k)| >= 1) as H12. { assert ((k <= -1)%Z \/ (k = 0)%Z \/ (k >= 1)%Z) as [H13 | [H13 | H13]] by lia; [apply IZR_le in H13; solve_R | lia | apply IZR_ge in H13; solve_R]. }
            pose proof π_pos as H13. nra.
        }
        rewrite <- H8. unfold sin_0_2π. destruct (Rle_dec z π) as [H9 | H9]; pose proof π_pos as H10; solve_R.
    - eapply derivative_at_ext_val.
      + apply derivative_at_neg.
        apply derivative_at_comp with (f := fun z => 2 * π - z) (g := sin_0_π).
        * apply derivative_at_minus; [apply derivative_at_const | apply derivative_at_id].
        * apply H1. lra.
      + unfold compose. simpl.
        pose proof (cos_on_π_2π y H4) as H5. lra.
  }
  assert (H4 : forall y, ⟦ der y ⟧ sin = cos -> ⟦ der (y + 2 * π) ⟧ sin = cos).
  {
    intros y H5.
    apply derivative_at_eq with (f1 := fun z => sin (z - 2 * π)).
    - exists 1. split; [lra |]. intros z H6. rewrite <- sin_periodic.
      replace (z - 2 * π + 2 * π) with z by lra. reflexivity.
    - eapply derivative_at_ext_val.
      + apply derivative_at_comp with (f := fun z => z - 2 * π) (g := sin).
        * apply derivative_at_minus; [apply derivative_at_id | apply derivative_at_const].
        * replace (y + 2 * π - 2 * π) with y by lra. exact H5.
      + unfold compose. replace (y + 2 * π - 2 * π) with y by lra.
        pose proof (cos_periodic y) as H6. lra.
  }
  assert (H5 : forall y, ⟦ der (y + 2 * π) ⟧ sin = cos -> ⟦ der y ⟧ sin = cos).
  {
    intros y H6.
    apply derivative_at_eq with (f1 := fun z => sin (z + 2 * π)).
    - exists 1. split; [lra |]. intros z H7. apply sin_periodic.
    - eapply derivative_at_ext_val.
      + apply derivative_at_comp with (f := fun z => z + 2 * π) (g := sin).
        * apply derivative_at_plus; [apply derivative_at_id | apply derivative_at_const].
        * exact H6.
      + unfold compose. pose proof (cos_periodic y) as H7. lra.
  }
  assert (H6 : ⟦ der 0 ⟧ sin = cos).
  {
    eapply derivative_at_ext_val.
    - apply limit_derivative_imp_derivative_at with (f' := cos).
      + unfold continuous_at. rewrite sin_0. apply limit_sin_0.
      + exists π. split; [pose proof π_pos as H7; lra |].
        intros y H7 H8.
        assert (0 < y < π \/ -π < y < 0) as [H9 | H9] by solve_R.
        * apply H2; auto.
        * apply H5. apply H3. pose proof π_pos as H10; lra.
      + apply limit_cos.
    - simpl. reflexivity.
  }
  assert (H7 : ⟦ der π ⟧ sin = cos).
  {
    eapply derivative_at_ext_val.
    - apply limit_derivative_imp_derivative_at with (f' := cos).
      + unfold continuous_at. rewrite sin_π. apply limit_sin_π.
      + exists π. split; [pose proof π_pos as H8; lra |].
        intros y H8 H9.
        assert (0 < y < π \/ π < y < 2 * π) as [H10 | H10] by solve_R.
        * apply H2; auto.
        * apply H3; auto.
      + apply limit_cos.
    - simpl. reflexivity.
  }
  destruct (red_0_2π_spec x) as [H8 [k H9]].
  set (y := proj1_sig (red_0_2π x)) in *.
  assert (H10 : ⟦ der y ⟧ sin = cos).
  {
    assert (y = 0 \/ 0 < y < π \/ y = π \/ π < y < 2 * π) as [H10 | [H10 | [H10 | H10]]] by solve_R.
    - rewrite H10. exact H6.
    - apply H2; auto.
    - rewrite H10. exact H7.
    - apply H3; auto.
  }
  apply derivative_at_eq with (f1 := fun z => sin (z - IZR k * 2 * π)).
  - exists 1. split; [lra |]. intros z H11.
    unfold sin.
    destruct (red_0_2π_spec z) as [H12 [k1 H13]].
    destruct (red_0_2π_spec (z - IZR k * 2 * π)) as [H14 [k2 H15]].
    set (z1 := proj1_sig (red_0_2π z)) in *.
    set (z2 := proj1_sig (red_0_2π (z - IZR k * 2 * π))) in *.
    assert (H16 : z1 = z2).
    {
      assert (|(z1 - z2)| < 2 * π) as H16 by solve_R.
      rewrite H13 in H15.
      replace (z1 - z2) with ((IZR k2 - IZR k1 + IZR k) * 2 * π) in H16 by lra.
      set (m := (k2 - k1 + k)%Z).
      replace (IZR k2 - IZR k1 + IZR k) with (IZR m) in H16.
      2: { unfold m. repeat rewrite plus_IZR; repeat rewrite minus_IZR; lra. }
      assert (|(IZR m * 2 * π)| = |(IZR m)| * 2 * π) as H17 by solve_R.
      rewrite H17 in H16.
      destruct (Z.eq_dec m 0) as [H18 | H18].
      - assert (k2 = (k1 - k)%Z) as H19 by lia.
        rewrite H19 in H15. rewrite minus_IZR in H15. lra.
      - assert (|(IZR m)| >= 1) as H19.
        { assert ((m <= -1)%Z \/ (m = 0)%Z \/ (m >= 1)%Z) as [H20 | [H20 | H20]] by lia.
          - apply IZR_le in H20. solve_R.
          - lia.
          - apply IZR_ge in H20. solve_R. }
        pose proof π_pos as H20. nra.
    }
    rewrite H16. reflexivity.
  - eapply derivative_at_ext_val.
    + apply derivative_at_comp with (f := fun z => z - IZR k * 2 * π) (g := sin).
      * apply derivative_at_minus; [apply derivative_at_id | apply derivative_at_const].
      * replace (x - IZR k * 2 * π) with y by lra. exact H10.
    + unfold compose. replace (x - IZR k * 2 * π) with y by lra.
      unfold cos.
      destruct (red_0_2π_spec x) as [H11 [k1 H12]].
      destruct (red_0_2π_spec y) as [H13 [k2 H14]].
      set (y1 := proj1_sig (red_0_2π x)) in *.
      set (y2 := proj1_sig (red_0_2π y)) in *.
      assert (H15 : y1 = y2).
      {
        assert (|(y1 - y2)| < 2 * π) as H15 by solve_R.
        rewrite H9 in H12. rewrite H14 in H12.
        replace (y1 - y2) with ((IZR k2 - IZR k1 + IZR k) * 2 * π) in H15 by lra.
        set (m := (k2 - k1 + k)%Z).
        replace (IZR k2 - IZR k1 + IZR k) with (IZR m) in H15.
        2: { unfold m. repeat rewrite plus_IZR; repeat rewrite minus_IZR; lra. }
        assert (|(IZR m * 2 * π)| = |(IZR m)| * 2 * π) as H16 by solve_R.
        rewrite H16 in H15.
        destruct (Z.eq_dec m 0) as [H17 | H17].
        - assert (k1 = (k2 + k)%Z) as H18 by lia.
          rewrite H18 in H12. rewrite plus_IZR in H12. lra.
        - assert (|(IZR m)| >= 1) as H18.
          { assert ((m <= -1)%Z \/ (m = 0)%Z \/ (m >= 1)%Z) as [H19 | [H19 | H19]] by lia.
            - apply IZR_le in H19. solve_R.
            - lia.
            - apply IZR_ge in H19. solve_R. }
          pose proof π_pos as H19. nra.
      }
      rewrite H15. lra.
Qed.

Lemma derivative_sin :
  ⟦ der ⟧ sin = cos.
Proof.
  intros x.
  apply derivative_at_sin.
Qed.

Lemma pythagorean_identity : ∀ x, (sin x)^2 + (cos x)^2 = 1.
Proof.
  intros x. unfold sin, cos.
  destruct (red_0_2π_spec x) as [H1 [k H2]].
  set (y := proj1_sig (red_0_2π x)) in *.
  assert (H3: 0 <= y < 2 * π) by (apply red_0_2π_spec).
  unfold sin_0_2π, cos_0_2π.
  destruct (Rle_dec y π) as [H4 | H4].
  - apply pythagorean_identity_0_π; lra.
  - replace ((- sin_0_π (2 * π - y)) ^ 2) with ((sin_0_π (2 * π - y)) ^ 2) by lra.
    apply pythagorean_identity_0_π. lra.
Qed.

Lemma derivative_at_tan : forall x,
  cos x ≠ 0 -> ⟦ der x ⟧ tan = sec ^ 2.
Proof.
  intros x H1. unfold tan. 
  replace (sec ^ 2)%function with ((λ x : ℝ, (cos x * cos x - (- sin x) * sin x) / (cos x * cos x))).
  2 : { extensionality y. unfold sec. assert (cos y = 0 \/ cos y <> 0) as [H2 | H2] by lra.
        - rewrite H2. rewrite Rmult_0_r, Rdiv_0_r, Rdiv_0_r. lra.
        - field_simplify; auto. pose proof pythagorean_identity y as H3. 
          rewrite Rplus_comm in H3. rewrite <- H3. reflexivity.
        }
  apply derivative_at_div; auto.
  - apply derivative_sin.
  - apply derivative_cos.
Qed.

Lemma differentiable_sin : differentiable sin.
Proof.
  intros x.
  apply derivative_at_imp_differentiable_at with (f' := cos).
  apply derivative_at_sin.
Qed.

Lemma continuous_sin : continuous sin.
Proof.
  apply differentiable_imp_continuous.
  apply differentiable_sin.
Qed.

Lemma sin_π_over_2 : sin (π / 2) = 1.
Proof.
  pose proof π_pos as H1.
  assert (H2: 0 <= π / 2 <= π) by lra.
  rewrite sin_consistency_on_0_π; auto.
  unfold sin_0_π.
  assert (H3 : cos_0_π (π / 2) = 0).
  { rewrite <- cos_on_0_π; auto. apply cos_π_over_2. }
  rewrite H3. replace (1 - 0 ^ 2) with 1 by lra. apply sqrt_1.
Qed.

Lemma sin_increasing_on : increasing_on sin [-(π/2), π/2].
Proof.
  apply derivative_on_pos_imp_increasing_on_open with (f' := cos); try (pose proof π_pos; lra).
  - apply continuous_on_subset_closed with (a := -(π/2)) (b := π/2); try (pose proof π_pos; lra).
    apply continuous_imp_continuous_on. apply continuous_sin.
  - apply derivative_imp_derivative_on.
    + apply differentiable_domain_open; pose proof π_pos; lra.
    + apply derivative_sin.
  - intros x H1. simpl.
    pose proof π_pos as H2.
    assert (0 < x < π / 2 \/ x = 0 \/ - (π / 2) < x < 0) as [H3 | [H3 | H3]].
    + destruct H1; lra.
    + rewrite cos_on_0_π; try lra.
      assert (H4 : cos_0_π x <= 0 \/ cos_0_π x > 0) by lra. destruct H4 as [H4 | H4]; try lra.
      assert (H5 : cos_0_π x = 0 \/ cos_0_π x < 0) by lra. destruct H5 as [H5 | H5].
      * pose proof cos_0_π_spec x as H6. assert (0 <= x <= π) as H7 by lra. specialize (H6 H7). rewrite H5 in H6. rewrite A_at_0 in H6. lra.
      * assert (H6 : cos_0_π x ∈ [-1, 1]). { apply cos_0_π_in_range; lra. }
        assert (H7 : 0 ∈ [-1, 1]) by (split; lra).
        pose proof A_decreases (cos_0_π x) 0 H6 H7 H5 as H8.
        pose proof cos_0_π_spec x as H9. assert (0 <= x <= π) as H10 by lra. specialize (H9 H10).
        rewrite H9 in H8. rewrite A_at_0 in H8. lra.
    + subst. rewrite cos_0. lra.
    + assert (H4 : cos x = cos (x + 2 * π)). { symmetry. apply cos_periodic. } rewrite H4. 
      assert (H5 : π < x + 2 * π < 2 * π) by lra. rewrite cos_on_π_2π; try lra. replace (2 * π - (x + 2 * π)) with (- x) by lra.
      assert (H6 : cos_0_π (-x) <= 0 \/ cos_0_π (-x) > 0) by lra. destruct H6 as [H6 | H6]; try lra. 
      assert (H7 : cos_0_π (-x) = 0 \/ cos_0_π (-x) < 0) by lra. destruct H7 as [H7 | H7].
      * pose proof cos_0_π_spec (-x) as H8. assert (0 <= -x <= π) as H9 by lra. specialize (H8 H9). rewrite H7 in H8. rewrite A_at_0 in H8. lra.
      * assert (H8 : cos_0_π (-x) ∈ [-1, 1]). { apply cos_0_π_in_range; lra. }
        assert (H9 : 0 ∈ [-1, 1]) by (split; lra).
        pose proof A_decreases (cos_0_π (-x)) 0 H8 H9 H7 as H10.
        pose proof cos_0_π_spec (-x) as H11. assert (0 <= -x <= π) as H12 by lra. specialize (H11 H12).
        rewrite H11 in H10. rewrite A_at_0 in H10. lra.
Qed.

Lemma cos_decreasing_on : decreasing_on cos [0, π].
Proof.
  apply derivative_on_neg_imp_decreasing_on_open with (f' := (- sin)%function); try (pose proof π_pos; lra).
  - apply continuous_on_subset_closed with (a := 0) (b := π); try (pose proof π_pos; lra).
    apply continuous_imp_continuous_on. apply continuous_cos.
  - apply derivative_imp_derivative_on. pose proof π_pos as H1. apply differentiable_domain_open; lra. apply derivative_cos.
  - intros x H1. simpl.
    assert (H2 : 0 <= x <= π). { destruct H1 as [H3 H4]; lra. }
    assert (H3: 0 < sin_0_π x).
    {
      unfold sin_0_π. apply sqrt_lt_R0.
      assert (H4: cos_0_π x ∈ [-1, 1]). { apply cos_0_π_in_range; lra. }
      assert (H5: cos_0_π x <> 1).
      {
        intro H6.
        pose proof cos_0_π_spec x ltac:(lra) as H7.
        rewrite H6 in H7. rewrite A_at_1 in H7. solve_R.
      }
      assert (H6: cos_0_π x <> -1).
      {
        intro H7.
        pose proof cos_0_π_spec x ltac:(lra) as H8.
        rewrite H7 in H8. rewrite A_at_neg_1 in H8. solve_R.
      }
      destruct H4 as [H7 H8]; nra.
    }
    assert (H4: sin x = sin_0_π x).
    { apply sin_consistency_on_0_π; lra. }
    rewrite H4. lra.
Qed.

Lemma continuous_on_tan : continuous_on tan (-π / 2, π / 2).
Proof.
  apply differentiable_on_imp_continuous_on_open.
  - pose proof π_pos as H1. lra.
  - apply derivative_on_imp_differentiable_on with (f' := (sec ^ 2)%function).
    intros x H1. left. split; [auto_interval |].
    apply derivative_at_tan.
    intro H2.
    pose proof pythagorean_identity x as H3.
    rewrite H2 in H3.
    assert (H4 : sin x = 1 \/ sin x = -1) by nra.
    pose proof sin_increasing_on as H5.
    assert (H6 : - (π / 2) <= x <= π / 2) by solve_R.
    assert (H7 : - (π / 2) <= π / 2 <= π / 2) by (pose proof π_pos; lra).
    assert (H8 : - (π / 2) <= - (π / 2) <= π / 2) by (pose proof π_pos; lra).
    destruct H4 as [H4 | H4].
    + pose proof H5 x (π/2) H6 H7 ltac:(solve_R) as H9.
      rewrite H4, sin_π_over_2 in H9. lra.
    + pose proof H5 (- (π / 2)) x H8 H6 ltac:(solve_R) as H9.
      pose proof pythagorean_identity (- (π / 2)) as H10.
      nra.
Qed.

Lemma tan_increasing_on : increasing_on tan (-(π/2), π/2).
Proof.
  intros x y H1 H2 H3.
  assert (H4 : forall z, z ∈ (-(π/2), π/2) -> cos z <> 0).
  {
    intros z H5 H6.
    pose proof pythagorean_identity z as H7.
    rewrite H6 in H7.
    assert (H8 : sin z = 1 \/ sin z = -1) by nra.
    pose proof sin_increasing_on as H9.
    assert (H10 : - (π / 2) <= z <= π / 2) by solve_R.
    assert (H11 : - (π / 2) <= π / 2 <= π / 2) by (pose proof π_pos; lra).
    assert (H12 : - (π / 2) <= - (π / 2) <= π / 2) by (pose proof π_pos; lra).
    destruct H8 as [H8 | H8].
    - pose proof H9 z (π/2) H10 H11 ltac:(solve_R) as H13.
      rewrite H8, sin_π_over_2 in H13. lra.
    - pose proof H9 (- (π / 2)) z H12 H10 ltac:(solve_R) as H13.
      pose proof pythagorean_identity (- (π / 2)) as H14.
      nra.
  }
  assert (H5 : increasing_on tan [x, y]).
  {
    apply derivative_on_pos_imp_increasing_on_open with (f' := (sec ^ 2)%function); auto.
    - apply continuous_on_subset with (A2 := (-(π/2), π/2)); auto.
      + intros z H6. solve_R.
      + replace (- (π / 2)) with (-π/2) by lra. apply continuous_on_tan.
    - apply derivative_at_imp_derivative_on.
      + apply differentiable_domain_open; solve_R.
      + intros z H6. apply derivative_at_tan. apply H4. solve_R.
    - intros z H6. unfold sec. apply pow2_gt_0.
      intro H7.
      assert (H8 : 1 / cos z * cos z = 0 * cos z) by (f_equal; lra).
      assert (H9 : cos z <> 0) by (apply H4; solve_R).
      assert (H10 : 1 / cos z * cos z = 1) by (field; auto).
      lra.
  }
  apply H5; solve_R.
Qed.

Lemma sin_bounds : forall x,
  -1 <= sin x <= 1.
Proof.
  intros x.
  pose proof (pythagorean_identity x).
  nra.
Qed.

Lemma sin_3_π_over_2 : sin (3 * π / 2) = -1.
Proof.
  pose proof π_pos as H1.
  unfold sin.
  destruct (red_0_2π_spec (3 * π / 2)) as [H2 [k H3]].
  set (y := proj1_sig (red_0_2π (3 * π / 2))) in *.
  assert (H4: 3 * π / 2 = y).
  {
    assert (|(3 * π / 2 - y)| < 2 * π) as H4 by solve_R.
    rewrite H3 in H4.
    replace (y + IZR k * 2 * π - y) with (IZR k * 2 * π) in H4 by lra.
    assert (|(IZR k * 2 * π)| = (|(IZR k)| * 2 * π)) as H5 by solve_R.
    rewrite H5 in H4.
    destruct (Z.eq_dec k 0) as [H6 | H6].
    - rewrite H6 in *. lra.
    - assert (|(IZR k)| >= 1) as H7. 
      {
        assert ((k <= -1)%Z \/ (k = 0)%Z \/ (k >= 1)%Z) as [H8 | [H8 | H8]] by lia.
        - apply IZR_le in H8. solve_R.
        - rewrite H8 in *. lia.
        - apply IZR_ge in H8. solve_R.
      }
      nra.
  }
  rewrite <- H4.
  unfold sin_0_2π.
  destruct (Rle_dec (3 * π / 2) π) as [H5 | H5]; try lra.
  replace (2 * π - 3 * π / 2) with (π / 2) by lra.
  assert (H6: 0 <= π / 2 <= π) by lra.
  rewrite <- (sin_consistency_on_0_π (π / 2) H6).
  rewrite sin_π_over_2.
  lra.
Qed.

Lemma sin_bijective : bijective_on sin [- (π / 2), π / 2] [-1, 1].
Proof.
  split; [| split].
  - intros x H1. pose proof sin_bounds x. solve_R.
  - apply increasing_on_imp_one_to_one_on. apply sin_increasing_on.
  - intros y H1. assert (y = -1 \/ y = 1 \/ -1 < y < 1) as [H2 | [H2 | H2]] by solve_R.
    + exists (-π/2). split.
      * pose proof π_pos; solve_R.
      * pose proof sin_periodic (-π/2) as H3. replace (- π / 2 + 2 * π) with (3 * π / 2) in H3 by lra.
       rewrite <- H3. rewrite sin_3_π_over_2. solve_R.
    + exists (π/2). split.
      * pose proof π_pos; solve_R.
      * rewrite sin_π_over_2. auto.
    + pose proof intermediate_value_theorem sin (-π/2) (π/2) y as [x [H3 H4]].
      * pose proof π_pos as H3. lra.
      * apply continuous_imp_continuous_on, continuous_sin.
      * rewrite sin_π_over_2. pose proof sin_periodic (-π/2) as H3. replace (- π / 2 + 2 * π) with (3 * π / 2) in H3 by lra.
        rewrite <- H3. rewrite sin_3_π_over_2. solve_R.
      * exists x; split; solve_R.
Qed.

Lemma cos_bounds : forall x,
  -1 <= cos x <= 1.
Proof.
  intros x.
  pose proof (pythagorean_identity x).
  nra.
Qed.

Lemma cos_bijective : bijective_on cos [0, π] [-1, 1].
Proof.
  split; [| split].
  - intros x H1. pose proof cos_bounds x. solve_R.
  - apply decreasing_on_imp_one_to_one_on. apply cos_decreasing_on.
  - intros y H1. assert (y = -1 \/ y = 1 \/ -1 < y < 1) as [H2 | [H2 | H2]] by solve_R.
    + exists π. split.
      * pose proof π_pos; solve_R.
      * rewrite cos_π. auto.
    + exists 0. split.
      * pose proof π_pos; solve_R.
      * rewrite cos_0. auto.
    + pose proof intermediate_value_theorem_decreasing cos 0 π y as [x [H3 H4]].
      * pose proof π_pos as H3. lra.
      * apply continuous_imp_continuous_on, continuous_cos.
      * rewrite cos_0, cos_π. solve_R.
      * exists x; split; solve_R.
Qed.

Lemma exists_sin_inverse : exists f, inverse_on sin f [-(π/2), π/2] [-1, 1].
Proof.
  pose proof sin_bijective as H1.
  pose proof exists_inverse_on_iff sin [-(π/2), π/2] [-1, 1] as H2.
  apply H2; auto.
Qed.

Lemma exists_cos_inverse : exists f, inverse_on cos f [0, π] [-1, 1].
Proof.
  pose proof cos_bijective as H1.
  pose proof exists_inverse_on_iff cos [0, π] [-1, 1] as H2.
  apply H2; auto.
Qed.

Definition arcsin_sig : {f : R -> R | inverse_on sin f [-(π/2), π/2] [-1, 1]}.
Proof.
  apply constructive_indefinite_description, exists_sin_inverse.
Qed.

Definition arccos_sig : {f : R -> R | inverse_on cos f [0, π] [-1, 1]}.
Proof.
  apply constructive_indefinite_description, exists_cos_inverse.
Qed.

Definition arcsin (y : R) : R := proj1_sig arcsin_sig y.

Definition arccos (y : R) : R := proj1_sig arccos_sig y.

Lemma arcsin_spec : inverse_on sin arcsin [-(π/2), π/2] [-1, 1].
Proof.
  unfold arcsin. destruct arcsin_sig as [f_inv H1]. auto.
Qed.

Lemma arccos_spec : inverse_on cos arccos [0, π] [-1, 1].
Proof.
  unfold arccos. destruct arccos_sig as [f_inv H1]. auto.
Qed.

Lemma cos_sign_q1 : ∀ x, 0 <= x <= π/2 -> 0 <= cos x.
Proof.
  intros x H1. rewrite cos_on_0_π; try lra.
  apply Rnot_lt_le. intro H2.
  assert (H3: cos_0_π x < 0) by lra.
  assert (H5: cos_0_π x ∈ [-1, 1]). { apply cos_0_π_in_range; lra. }
  assert (H6: 0 ∈ [-1, 1]) by (split; lra).
  apply (A_decreases (cos_0_π x) 0) in H3; try assumption.
  rewrite cos_0_π_spec in H3; try lra.
  rewrite A_at_0 in H3.
  lra.
Qed.

Lemma cos_sign_q2 : ∀ x, π/2 <= x <= π -> cos x <= 0.
Proof.
  intros x H1. rewrite cos_on_0_π; try lra.
  apply Rnot_gt_le. intro H2.
  assert (H3: cos_0_π x > 0) by lra.
  assert (H5: cos_0_π x ∈ [-1, 1]). { apply cos_0_π_in_range; lra. }
  assert (H6: 0 ∈ [-1, 1]) by (split; lra).
  apply (A_decreases 0 (cos_0_π x)) in H3; try assumption.
  rewrite cos_0_π_spec in H3; try lra.
  rewrite A_at_0 in H3.
  lra.
Qed.

Lemma cos_sign_q3 : ∀ x, π <= x <= (3*π)/2 -> cos x <= 0.
Proof.
  intros x H1.
  pose proof π_pos as H2.
  assert (x = π \/ π < x) as [H3 | H3] by lra.
  - subst x. apply cos_sign_q2. lra.
  - assert (H4 : π < x < 2 * π) by lra.
    rewrite cos_on_π_2π; auto.
    assert (H5 : 0 <= 2 * π - x <= π) by lra.
    rewrite <- (cos_on_0_π (2 * π - x) H5).
    apply cos_sign_q2. lra.
Qed.

Lemma cos_sign_q4 : ∀ x, (3*π)/2 <= x <= 2 * π -> 0 <= cos x.
Proof.
  intros x H1.
  pose proof π_pos as H2.
  assert (x = 2 * π \/ x < 2 * π) as [H3 | H3] by lra.
  - subst x.
    replace (2 * π) with (0 + 2 * π) by lra.
    rewrite cos_periodic.
    rewrite cos_0. lra.
  - assert (H4 : π < x < 2 * π) by lra.
    rewrite cos_on_π_2π; auto.
    assert (H5 : 0 <= 2 * π - x <= π) by lra.
    rewrite <- (cos_on_0_π (2 * π - x) H5).
    apply cos_sign_q1. lra.
Qed.

Lemma tan_bijective : bijective_on tan (-(π / 2), π / 2) R.
Proof.
  split; [| split].
  - intros x H1. apply Full_intro.
  - apply increasing_on_imp_one_to_one_on. apply tan_increasing_on.
  - intros y H1.
    set (u := y / √(1 + y^2)).
    assert (H2 : 1 + y^2 > 0) by nra.
    assert (H3 : √(1 + y^2) > 0) by (apply sqrt_lt_R0; lra).
    assert (H4 : u^2 < 1).
    {
      unfold u.
      replace ((y / √(1 + y^2)) ^ 2) with (y^2 / (√(1 + y^2) ^ 2)) by (field; lra).
      rewrite pow2_sqrt; try lra.
      apply Rmult_lt_reg_r with (r := 1 + y^2); try lra.
      replace (y^2 / (1 + y^2) * (1 + y^2)) with (y^2) by (field; lra).
      lra.
    }
    assert (H5 : u ∈ [-1, 1]) by (split; nra).
    pose proof arcsin_spec as [H6 [H7 [H8 H9]]].
    set (x := arcsin u).
    assert (H10 : x ∈ [- (π / 2), π / 2]) by (apply H7; auto).
    assert (H11 : sin x = u) by (apply H9; auto).
    assert (H12 : - (π / 2) < x < π / 2).
    {
      destruct H10 as [H10a H10b].
      assert (x = π / 2 \/ x < π / 2) as [H13 | H13] by lra.
      - rewrite H13 in H11. rewrite sin_π_over_2 in H11.
        assert (1 = u^2) by nra. lra.
      - assert (x = - (π / 2) \/ - (π / 2) < x) as [H14 | H14] by lra.
        + rewrite H14 in H11.
          assert (H15 : sin (- (π / 2)) = -1).
          {
            rewrite <- sin_periodic.
            replace (- (π / 2) + 2 * π) with (3 * π / 2) by lra.
            apply sin_3_π_over_2.
          }
          rewrite H15 in H11.
          assert (1 = u^2) by nra. lra.
        + split; lra.
    }
    exists x. split; [exact H12 |].
    unfold tan. rewrite H11.
    assert (H13 : 0 <= cos x).
    {
      assert (0 <= x <= π / 2 \/ - (π / 2) <= x < 0) as [H14 | H14] by lra.
      - apply cos_sign_q1; lra.
      - rewrite <- cos_periodic. apply cos_sign_q4.
        pose proof π_pos; lra.
    }
    assert (H14 : (cos x)^2 = 1 / (1 + y^2)).
    {
      pose proof pythagorean_identity x as H15.
      rewrite H11 in H15.
      assert (H16 : u^2 = y^2 / (1 + y^2)).
      {
        unfold u.
        replace ((y / √(1 + y^2)) ^ 2) with (y^2 / (√(1 + y^2) ^ 2)) by (field; lra).
        rewrite pow2_sqrt; lra.
      }
      rewrite H16 in H15.
      replace (cos x ^ 2) with (1 - y^2 / (1 + y^2)) by lra.
      field; lra.
    }
    assert (H15 : cos x = 1 / √(1 + y^2)).
    {
      assert (H16 : (1 / √(1 + y^2))^2 = 1 / (1 + y^2)).
      {
        replace ((1 / √(1 + y^2))^2) with (1 / (√(1 + y^2)^2)) by (field; lra).
        rewrite pow2_sqrt; lra.
      }
      assert (H17 : 0 <= 1 / √(1 + y^2)). { apply Rlt_le. apply Rdiv_pos_pos; lra. }
      nra.
    }
    rewrite H15. unfold u.
    field. lra.
Qed.

Lemma exists_tan_inverse : exists f, inverse_on tan f (-(π / 2), π / 2) R.
Proof.
  pose proof tan_bijective as H1.
  pose proof exists_inverse_on_iff tan (-(π / 2), π / 2) R as H2.
  apply H2; auto.
Qed.

Definition arctan_sig : {f : R -> R | inverse_on tan f (-(π / 2), π / 2) R}.
Proof.
  apply constructive_indefinite_description, exists_tan_inverse.
Qed.

Definition arctan (y : R) : R := proj1_sig arctan_sig y.

Lemma arctan_spec : inverse_on tan arctan (-(π / 2), π / 2) R.
Proof.
  unfold arctan. destruct arctan_sig as [f_inv H1]. auto.
Qed.

Theorem theorem_4 : forall f f' f'' a b,
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ f' = f'' ->
  (forall x, f'' x + f x = 0) ->
  f 0 = a ->
  f' 0 = b ->
  forall x, f x = b * sin x + a * cos x.
Proof.
  intros f f' f'' a b H1 H2 H3 H4 H5 x.
  set (g := fun x => f x - (b * sin x + a * cos x)).
  set (g' := fun x => f' x - (b * cos x - a * sin x)).
  set (g'' := fun x => f'' x - (- b * sin x - a * cos x)).
  assert (⟦ der ⟧ g = g') as H6.
  {
    unfold g, g'. apply derivative_minus; auto.
    apply derivative_ext with (f1' := (fun x => b * cos x + a * (- sin x))).
    { intros y. lra. }
    apply derivative_plus. apply derivative_mult_const_l. apply derivative_sin.
    apply derivative_mult_const_l. apply derivative_cos.
  }
  assert (⟦ der ⟧ g' = g'') as H7.
  {
    unfold g', g''. apply derivative_minus; auto.
    apply derivative_ext with (f1' := (fun x => b * (- sin x) + -a * cos x)).
    { intros y. lra. }
    apply derivative_plus. apply derivative_mult_const_l. apply derivative_cos.
    replace (fun x => - (a * sin x)) with (fun x => - a * sin x) by (extensionality y; lra).
    apply derivative_mult_const_l. apply derivative_sin.
  }
  assert (forall y, g'' y + g y = 0) as H8.
  { intro y. unfold g, g''. specialize (H3 y). lra. }
  assert (g 0 = 0) as H9.
  { unfold g. rewrite H4, sin_0, cos_0. lra. }
  assert (g' 0 = 0) as H10.
  { unfold g'. rewrite H5, sin_0, cos_0. lra. }
  pose proof zero_differential_eq_2nd_order g g' g'' H6 H7 H8 H9 H10 x as H11.
  unfold g in H11. lra.
Qed.

Lemma sin_plus : forall x y,
  sin (x + y) = sin x * cos y + cos x * sin y.
Proof.
  intros x y.
  set (f := fun t => sin (t + y)).
  set (f' := fun t => cos (t + y)).
  set (f'' := fun t => - sin (t + y)).
  pose proof theorem_4 f f' f'' (sin y) (cos y) as H1.
  assert (⟦ der ⟧ f = f') as H2.
  {
    unfold f, f'.
    apply derivative_ext with (f1' := (fun u => cos (u + y) * 1)).
    { intros z. lra. } apply (derivative_comp (fun u => u + y) sin (fun _ => 1) cos).
    - replace 1 with (1 + 0) by lra. apply derivative_plus; [apply derivative_id | apply derivative_const].
    - apply derivative_sin.
  }
  assert (⟦ der ⟧ f' = f'') as H3.
  {
    unfold f', f''.
    apply derivative_ext with (f1' := (fun u => - sin (u + y) * 1)).
    { intros z. lra. } apply (derivative_comp (fun u => u + y) cos (fun _ => 1) (- sin)).
    - replace 1 with (1 + 0) by lra. apply derivative_plus; [apply derivative_id | apply derivative_const].
    - apply derivative_cos.
  }
  specialize (H1 H2 H3).
  assert (forall t, f'' t + f t = 0) as H4 by (intro t; unfold f, f''; lra).
  specialize (H1 H4).
  assert (f 0 = sin y) as H5 by (unfold f; replace (0 + y) with y by lra; reflexivity).
  assert (f' 0 = cos y) as H6 by (unfold f'; replace (0 + y) with y by lra; reflexivity).
  specialize (H1 H5 H6 x).
  unfold f in H1. rewrite H1. lra.
Qed.

Lemma cos_plus : forall x y,
  cos (x + y) = cos x * cos y - sin x * sin y.
Proof.
  intros x y.
  set (f := fun t => cos (t + y)).
  set (f' := fun t => - sin (t + y)).
  set (f'' := fun t => - cos (t + y)).
  pose proof theorem_4 f f' f'' (cos y) (- sin y) as H1.
  assert (⟦ der ⟧ f = f') as H2.
  {
    unfold f, f'.
    apply derivative_ext with (f1' := (fun u => - sin (u + y) * 1)).
    { intros z. lra. } apply (derivative_comp (fun u => u + y) cos (fun _ => 1) (- sin)).
    - replace 1 with (1 + 0) by lra. apply derivative_plus; [apply derivative_id | apply derivative_const].
    - apply derivative_cos.
  }
  assert (⟦ der ⟧ f' = f'') as H3.
  {
    unfold f', f''.
    apply derivative_ext with (f1' := (fun u => - cos (u + y) * 1)).
    { intros z. lra. } apply (derivative_comp (fun u => u + y) (- sin) (fun _ => 1) (- cos)).
    - replace 1 with (1 + 0) by lra. apply derivative_plus; [apply derivative_id | apply derivative_const].
    - apply derivative_neg. apply derivative_sin.
  }
  specialize (H1 H2 H3).
  assert (forall t, f'' t + f t = 0) as H4 by (intro t; unfold f, f''; lra).
  specialize (H1 H4).
  assert (f 0 = cos y) as H5 by (unfold f; replace (0 + y) with y by lra; reflexivity).
  assert (f' 0 = - sin y) as H6 by (unfold f'; replace (0 + y) with y by lra; reflexivity).
  specialize (H1 H5 H6 x).
  unfold f in H1. rewrite H1. lra.
Qed.

Lemma tan_plus : forall x y,
  cos x <> 0 -> cos y <> 0 -> cos (x + y) <> 0 ->
  tan (x + y) = (tan x + tan y) / (1 - tan x * tan y).
Proof.
  intros x y H1 H2 H3.
  unfold tan. rewrite sin_plus, cos_plus.
  field. rewrite <- cos_plus. lra.
Qed.

Lemma arctan_plus : forall x y,
  x * y < 1 ->
  arctan x + arctan y = arctan ((x + y) / (1 - x * y)).
Proof.
  intros x y H1.
  pose proof arctan_spec as [H2 [H3 [H4 H5]]].
  assert (H6 : forall z, -(π/2) < z < π/2 -> cos z > 0).
  {
    intros z H6. pose proof π_pos as H7.
    assert (0 < z < π / 2 \/ z = 0 \/ - (π / 2) < z < 0) as [H8 | [H8 | H8]] by lra.
    - assert (H9 : z ∈ [0, π]) by (split; lra).
      assert (H10 : π / 2 ∈ [0, π]) by (split; lra).
      pose proof cos_decreasing_on z (π / 2) H9 H10 ltac:(lra) as H11.
      rewrite cos_π_over_2 in H11. lra.
    - subst. rewrite cos_0. lra.
    - assert (H9 : cos z = cos (z + 2 * π)). { symmetry. apply cos_periodic. } rewrite H9.
      assert (H10 : π < z + 2 * π < 2 * π) by lra. rewrite cos_on_π_2π; try lra. replace (2 * π - (z + 2 * π)) with (- z) by lra.
      assert (H11 : cos_0_π (-z) <= 0 \/ cos_0_π (-z) > 0) by lra. destruct H11 as [H11 | H11]; try lra.
      assert (H12 : cos_0_π (-z) = 0 \/ cos_0_π (-z) < 0) by lra. destruct H12 as [H12 | H12].
      + pose proof cos_0_π_spec (-z) as H13. assert (0 <= -z <= π) as H14 by lra. specialize (H13 H14). rewrite H12 in H13. rewrite A_at_0 in H13. lra.
      + assert (H13 : cos_0_π (-z) ∈ [-1, 1]). { apply cos_0_π_in_range; lra. }
        assert (H14 : 0 ∈ [-1, 1]) by (split; lra).
        pose proof A_decreases (cos_0_π (-z)) 0 H13 H14 H12 as H15.
        pose proof cos_0_π_spec (-z) as H16. assert (0 <= -z <= π) as H17 by lra. specialize (H16 H17).
        rewrite H16 in H15. rewrite A_at_0 in H15. lra.
  }
  assert (H7 : cos (arctan x) > 0).
  { apply H6. apply H3. apply Full_intro. }
  assert (H8 : cos (arctan y) > 0).
  { apply H6. apply H3. apply Full_intro. }
  assert (H9 : cos (arctan x + arctan y) > 0).
  {
    rewrite cos_plus.
    assert (H9 : tan (arctan x) = x) by (apply H5; apply Full_intro).
    assert (H10 : tan (arctan y) = y) by (apply H5; apply Full_intro).
    unfold tan in H9, H10.
    assert (H11 : sin (arctan x) = x * cos (arctan x)).
    { replace (sin (arctan x)) with ((sin (arctan x) / cos (arctan x)) * cos (arctan x)) by (field; lra).
      rewrite H9. reflexivity. }
    assert (H12 : sin (arctan y) = y * cos (arctan y)).
    { replace (sin (arctan y)) with ((sin (arctan y) / cos (arctan y)) * cos (arctan y)) by (field; lra).
      rewrite H10. reflexivity. }
    rewrite H11, H12.
    replace (cos (arctan x) * cos (arctan y) - x * cos (arctan x) * (y * cos (arctan y)))
      with (cos (arctan x) * cos (arctan y) * (1 - x * y)) by ring.
    apply Rmult_gt_0_compat.
    - apply Rmult_gt_0_compat; lra.
    - lra.
  }
  assert (H10 : (arctan x + arctan y) ∈ (-(π/2), π/2)).
  {
    assert (H10 : -(π/2) < arctan x < π/2) by (apply H3; apply Full_intro).
    assert (H11 : -(π/2) < arctan y < π/2) by (apply H3; apply Full_intro).
    assert (H12 : -π < arctan x + arctan y < π) by lra.
    set (S := arctan x + arctan y) in *.
    assert (S <= -(π/2) \/ -(π/2) < S < π/2 \/ π/2 <= S) as [H13 | [H13 | H13]] by lra.
    - assert (H14 : π <= S + 2 * π <= 3 * π / 2) by lra.
      pose proof π_pos as H15.
      assert (S + 2 * π = π \/ π < S + 2 * π) as [H17 | H17] by lra.
      + assert (cos S = -1). { rewrite <- cos_periodic, H17, cos_π. reflexivity. } lra.
      + assert (H18 : π < S + 2 * π < 2 * π) by lra.
        rewrite <- cos_periodic in H9. rewrite cos_on_π_2π in H9; auto.
        assert (H19 : 2 * π - (S + 2 * π) = - S) by lra. rewrite H19 in H9.
        assert (H20 : 0 <= - S <= π) by lra.
        rewrite <- cos_on_0_π in H9; auto.
        assert (H21 : - S = π / 2 \/ - S > π / 2) by lra.
        destruct H21 as [H22 | H22].
        * rewrite H22, cos_π_over_2 in H9. lra.
        * assert (H23 : π / 2 ∈ [0, π]) by (split; lra).
          assert (H24 : - S ∈ [0, π]) by (split; lra).
          pose proof cos_decreasing_on (π / 2) (- S) H23 H24 H22 as H25.
          rewrite cos_π_over_2 in H25. lra.
    - split; lra.
    - assert (H14 : π/2 <= S <= π) by lra.
      assert (H15 : S = π / 2 \/ S > π / 2) by lra.
      destruct H15 as [H16 | H16].
      + rewrite H16, cos_π_over_2 in H9. lra.
      + assert (H17 : π / 2 ∈ [0, π]) by (split; lra).
        assert (H18 : S ∈ [0, π]) by (split; lra).
        pose proof cos_decreasing_on (π / 2) S H17 H18 H16 as H19.
        rewrite cos_π_over_2 in H19. lra.
  }
  rewrite <- (H4 (arctan x + arctan y)); [ f_equal | exact H10 ].
  rewrite tan_plus; try lra.
  assert (H11 : tan (arctan x) = x) by (apply H5; apply Full_intro).
  assert (H12 : tan (arctan y) = y) by (apply H5; apply Full_intro).
  rewrite H11, H12. reflexivity.
Qed.

Lemma cos_π_over_4 : cos (π / 4) = √2 / 2.
Proof.
  pose proof π_pos as H1.
  assert (H2: cos (π / 2) = 0) by apply cos_π_over_2.
  replace (π / 2) with (π / 4 + π / 4) in H2 by lra.
  rewrite cos_plus in H2.
  assert (H3: (sin (π / 4))^2 = (cos (π / 4))^2) by nra.
  assert (H4: 0 <= π / 4 <= π) by lra.
  pose proof (pythagorean_identity_0_π (π / 4) H4) as H5.
  rewrite <- cos_on_0_π, <- sin_consistency_on_0_π in H5; auto.
  assert (H6: 2 * (cos (π / 4))^2 = 1) by nra.
  assert (H7: (√2 / 2)^2 = 1 / 2).
  { replace ((√2 / 2) ^ 2) with ((√2 ^ 2) / 4) by lra.
    rewrite pow2_sqrt; lra. }
  assert (H8: 0 <= cos (π / 4)) by (apply cos_sign_q1; lra).
  assert (H9: 0 <= √2 / 2) by (pose proof (sqrt_pos 2); lra).
  nra.
Qed.

Lemma sin_π_over_4 : sin (π / 4) = √2 / 2.
Proof.
  pose proof π_pos as H1.
  assert (H2: 0 <= π / 4 <= π) by lra.
  pose proof (pythagorean_identity_0_π (π / 4) H2) as H3.
  rewrite <- cos_on_0_π, <- sin_consistency_on_0_π in H3; auto.
  rewrite cos_π_over_4 in H3.
  assert (H4: (√2 / 2)^2 = 1 / 2).
  { replace ((√2 / 2) ^ 2) with ((√2 ^ 2) / 4) by lra.
    rewrite pow2_sqrt; lra. }
  assert (H5: 0 <= sin (π / 4)).
  { rewrite sin_consistency_on_0_π; auto. unfold sin_0_π. apply sqrt_pos. }
  assert (H6: 0 <= √2 / 2) by (pose proof (sqrt_pos 2); lra).
  nra.
Qed.

Lemma cos_gt_0_on_open_pi_2 : ∀ x, 0 < x < π/2 -> cos x > 0.
Proof.
  intros x H1.
  pose proof π_pos as H2.
  assert (H3 : x ∈ [0, π]) by (split; lra).
  assert (H4 : π / 2 ∈ [0, π]) by (split; lra).
  pose proof cos_decreasing_on x (π / 2) H3 H4 ltac:(lra) as H5.
  rewrite cos_π_over_2 in H5.
  lra.
Qed.

Lemma cos_derivative_on_0_π :
  ∀ x, 0 < x < π -> ⟦ der x ⟧ cos = - sin_0_π.
Proof.
  intros x Hx.
  apply derivative_at_eq with (f1 := cos_0_π).
  - exists (Rmin x (π - x)). split.
    + apply Rmin_pos; lra.
    + intros z Hz. rewrite cos_on_0_π; solve_R.
  - apply theorem_15_1_a; auto.
Qed.

Lemma sin2_plus_cos2 : ∀ x, (sin x)^2 + (cos x)^2 = 1.
Proof. exact pythagorean_identity. Qed.

Lemma tan_0 : tan 0 = 0.
Proof. 
  unfold tan. rewrite sin_0, cos_0. lra. 
Qed.

Lemma left_limit_sin : forall a,
  ⟦ lim a⁻ ⟧ sin = sin a.
Proof. intros a. apply continuous_at_imp_left_continuous. apply continuous_sin. Qed.

Lemma right_limit_sin : forall a,
  ⟦ lim a⁺ ⟧ sin = sin a.
Proof. intros a. apply continuous_at_imp_right_continuous. apply continuous_sin. Qed.

Lemma limit_sin : forall a,
  ⟦ lim a ⟧ sin = sin a.
Proof.
  intros a.
  apply limit_iff; split; [ apply left_limit_sin | apply right_limit_sin ].
Qed.

Lemma inf_differentiable_cos : inf_differentiable cos.
Proof.
  assert (H1 : forall f, 
    f = cos \/ f = sin \/ f = (fun x => -cos x) \/ f = (fun x => -sin x) ->
    exists f', derivative f f' /\ (f' = cos \/ f' = sin \/ f' = (fun x => -cos x) \/ f' = (fun x => -sin x))).
  {
    intros f [H2 | [H2 | [H2 | H2]]]; subst.
    - exists (- sin)%function. split; [apply derivative_cos | right; right; right; reflexivity].
    - exists cos. split; [apply derivative_sin | left; reflexivity].
    - exists sin. split. 
      + replace sin with (fun x => - (- sin x)) by (extensionality x; lra). 
        apply derivative_neg. apply derivative_cos.
      + right; left; reflexivity.
    - exists (- cos)%function. split; [apply derivative_neg; apply derivative_sin | right; right; left; reflexivity].
  }
  assert (H2 : forall n, exists fn, nth_derivative n cos fn /\ (fn = cos \/ fn = sin \/ fn = (fun x => -cos x) \/ fn = (fun x => -sin x))).
  {
    induction n as [| n H3].
    - exists cos. split; [simpl; reflexivity | left; reflexivity].
    - destruct H3 as [fk [H4 H5]].
      apply H1 in H5 as [fk' [H6 H7]].
      exists fk'. split; auto.
      simpl. exists fk. split; auto.
  }
  intros n. destruct (H2 n) as [fn [H3 H4]]. exists fn. apply H3.
Qed.

Lemma nth_derivative_cos_0 : ⟦ der^0 ⟧ cos = cos.
Proof.
  reflexivity.
Qed.

Lemma nth_derivative_sin_0 : ⟦ der^0 ⟧ sin = sin.
Proof.
  reflexivity.
Qed.

Lemma nth_derivative_cos_1 : ⟦ der^1 ⟧ cos = - sin.
Proof.
  apply nth_derivative_succ_iff. exists (- sin)%function. split.
  - apply derivative_cos.
  - reflexivity.
Qed.

Lemma nth_derivative_sin_1 : ⟦ der^1 ⟧ sin = cos.
Proof.
  apply nth_derivative_succ_iff. exists cos. split.
  - apply derivative_sin.
  - reflexivity.
Qed.

Lemma nth_derivative_cos_2 : ⟦ der^2 ⟧ cos = - cos.
Proof.
  apply nth_derivative_succ_iff.
  exists (fun x => - sin x).
  split.
  - apply derivative_cos.
  - simpl. exists (fun x => - sin x). split.
    + reflexivity.
    + apply derivative_neg. apply derivative_sin.
Qed.

Lemma nth_derivative_sin_2 : ⟦ der^2 ⟧ sin = - sin.
Proof.
  apply nth_derivative_succ_iff.
  exists cos. split.
  - apply derivative_sin.
  - simpl. exists (fun x => cos x). split; auto.
    apply derivative_cos.
Qed.

Lemma nth_derivative_cos_3 : ⟦ der^3 ⟧ cos = sin.
Proof.
  apply nth_derivative_succ_iff.
  exists (fun x => - sin x).
  split.
  - apply derivative_cos.
  - simpl. exists (fun x => - cos x). split.
    + exists (fun x => - sin x). split; [reflexivity |].
      apply derivative_neg. apply derivative_sin.
    + replace sin with (fun x => - (- sin x)) by (extensionality x; lra).
      apply derivative_neg. apply derivative_cos.
Qed.

Lemma nth_derivative_sin_3 : ⟦ der^3 ⟧ sin = - cos.
Proof.
  apply nth_derivative_succ_iff.
  exists cos. split.
  - apply derivative_sin.
  - simpl. exists (fun x => - sin x). split.
    + exists (fun x => cos x). split; [reflexivity |]. apply derivative_cos.
    + apply derivative_neg. apply derivative_sin.
Qed.

Lemma nth_derivative_cos_4 : ⟦ der^4 ⟧ cos = cos.
Proof.
  apply nth_derivative_succ_iff.
  exists (-sin)%function. split.
  - apply derivative_cos.
  - simpl. exists sin. split.
    + exists (fun x => - cos x). split.
      * exists (fun x => - sin x). split; auto.
        apply derivative_neg. apply derivative_sin.
      * replace sin with (fun x => - (- sin x)) by (extensionality x; lra).
        apply derivative_neg. apply derivative_cos.
    + apply derivative_sin.
Qed.

Lemma nth_derivative_sin_4 : ⟦ der^4 ⟧ sin = sin.
Proof.
  apply nth_derivative_succ_iff.
  exists cos. split.
  - apply derivative_sin.
  - simpl. exists (-cos)%function. split.
    + exists (-sin)%function. split.
      * exists cos. split; auto.
        apply derivative_cos.
      * apply derivative_neg. apply derivative_sin.
    + replace sin with (fun x => - (- sin x)) by (extensionality x; lra).
      apply derivative_neg. apply derivative_cos.
Qed.

Lemma nth_derivative_cos_4n : forall n, ⟦ der^(4 * n) ⟧ cos = cos.
Proof.
  induction n.
  - simpl. reflexivity.
  - replace (4 * S n)%nat with (4 * n + 4)%nat by lia.
    apply nth_derivative_add with cos; [auto | apply nth_derivative_cos_4].
Qed.

Lemma nth_derivative_sin_4n : forall n, ⟦ der^(4 * n) ⟧ sin = sin.
Proof.
  induction n.
  - simpl. reflexivity.
  - replace (4 * S n)%nat with (4 * n + 4)%nat by lia.
    apply nth_derivative_add with sin; [auto | apply nth_derivative_sin_4].
Qed.

Lemma nth_derivative_cos_4n_1 : forall n, ⟦ der^(4 * n + 1) ⟧ cos = -sin.
Proof.
  intros. apply nth_derivative_add with cos.
  - apply nth_derivative_cos_4n.
  - apply nth_derivative_cos_1.
Qed.

Lemma nth_derivative_sin_4n_1 : forall n, ⟦ der^(4 * n + 1) ⟧ sin = cos.
Proof.
  intros. apply nth_derivative_add with sin.
  - apply nth_derivative_sin_4n.
  - apply nth_derivative_sin_1.
Qed.

Lemma nth_derivative_cos_4n_2 : forall n, ⟦ der^(4 * n + 2) ⟧ cos = -cos.
Proof.
  intros. apply nth_derivative_add with cos.
  - apply nth_derivative_cos_4n.
  - apply nth_derivative_cos_2.
Qed.

Lemma nth_derivative_sin_4n_2 : forall n, ⟦ der^(4 * n + 2) ⟧ sin = -sin.
Proof.
  intros. apply nth_derivative_add with sin.
  - apply nth_derivative_sin_4n.
  - apply nth_derivative_sin_2.
Qed.

Lemma nth_derivative_cos_4n_3 : forall n, ⟦ der^(4 * n + 3) ⟧ cos = sin.
Proof.
  intros. apply nth_derivative_add with cos.
  - apply nth_derivative_cos_4n.
  - apply nth_derivative_cos_3.
Qed.

Lemma nth_derivative_sin_4n_3 : forall n, ⟦ der^(4 * n + 3) ⟧ sin = -cos.
Proof.
  intros. apply nth_derivative_add with sin.
  - apply nth_derivative_sin_4n.
  - apply nth_derivative_sin_3.
Qed.

Ltac normalize_nat_mod4 n :=
  let n' := eval cbv in n in
  let q  := eval cbv in (Nat.div n' 4) in
  let r  := eval cbv in (Nat.modulo n' 4) in
  lazymatch r with
  | O => replace n with (4 * q)%nat by lia
  | _ => replace n with (4 * q + r)%nat by lia
  end.

Ltac nat_mod4_normalize_derivative_only :=
  repeat match goal with
  | |- context[ nth_derivative ?n ?f ] =>
      normalize_nat_mod4 n
  | H : context[ nth_derivative ?n ?f ] |- _ =>
      normalize_nat_mod4 n

  | |- context[ nth_derive ?n ?f ] =>
      normalize_nat_mod4 n
  | H : context[ nth_derive ?n ?f ] |- _ =>
      normalize_nat_mod4 n

  | |- context[ nth_derive_at ?n ?f ?x ] =>
      normalize_nat_mod4 n
  | H : context[ nth_derive_at ?n ?f ?x ] |- _ =>
      normalize_nat_mod4 n
  end.


Ltac rewrite_trig_nth_derivative :=
  first
    [ apply nth_derivative_sin_4n
    | apply nth_derivative_sin_4n_1
    | apply nth_derivative_sin_4n_2
    | apply nth_derivative_sin_4n_3
    | apply nth_derivative_cos_4n
    | apply nth_derivative_cos_4n_1
    | apply nth_derivative_cos_4n_2
    | apply nth_derivative_cos_4n_3 ].


Ltac simplify_trig_derivatives :=
  repeat (first [ nat_mod4_normalize_derivative_only | rewrite_trig_nth_derivative ]).

Lemma nth_derive_cos_0 : 
  ⟦ Der^0 ⟧ cos = cos.
Proof.
  reflexivity.
Qed.

Lemma nth_derive_cos_1 : 
  ⟦ Der^1 ⟧ cos = (-sin)%function.
Proof.
  apply nth_derivative_imp_nth_derive. apply nth_derivative_cos_1.
Qed.

Lemma nth_derive_cos_2 : 
  ⟦ Der^2 ⟧ cos = (-cos)%function.
Proof.
  apply nth_derivative_imp_nth_derive. apply nth_derivative_cos_2.
Qed.

Lemma nth_derive_cos_3 : 
  ⟦ Der^3 ⟧ cos = sin.
Proof.
  apply nth_derivative_imp_nth_derive. apply nth_derivative_cos_3.
Qed.

Lemma nth_derive_cos_4 : 
  ⟦ Der^4 ⟧ cos = cos.
Proof.
  apply nth_derivative_imp_nth_derive. apply nth_derivative_cos_4.
Qed.

Lemma nth_derive_sin_0 : 
  ⟦ Der^0 ⟧ sin = sin.
Proof.
  reflexivity.
Qed.

Lemma nth_derive_sin_1 : 
  ⟦ Der^1 ⟧ sin = cos.
Proof.
  apply nth_derivative_imp_nth_derive. apply nth_derivative_sin_1.
Qed.

Lemma nth_derive_sin_2 : 
  ⟦ Der^2 ⟧ sin = (-sin)%function.
Proof.
  apply nth_derivative_imp_nth_derive. apply nth_derivative_sin_2.
Qed.

Lemma nth_derive_sin_3 : 
  ⟦ Der^3 ⟧ sin = (-cos)%function.
Proof.
  apply nth_derivative_imp_nth_derive. apply nth_derivative_sin_3.
Qed.

Lemma nth_derive_sin_4 : 
  ⟦ Der^4 ⟧ sin = sin.
Proof.
  apply nth_derivative_imp_nth_derive. apply nth_derivative_sin_4.
Qed.

Lemma nth_derive_cos_4n : forall n, ⟦ Der^(4 * n) ⟧ cos = cos.
Proof.
  intros n. apply nth_derivative_imp_nth_derive. apply nth_derivative_cos_4n.
Qed.

Lemma nth_derive_sin_4n : forall n, ⟦ Der^(4 * n) ⟧ sin = sin.
Proof.
  intros n. apply nth_derivative_imp_nth_derive. apply nth_derivative_sin_4n.
Qed.

Lemma nth_derive_cos_4n_1 : forall n, ⟦ Der^(4 * n + 1) ⟧ cos = (-sin)%function.
Proof.
  intros n. apply nth_derivative_imp_nth_derive. apply nth_derivative_cos_4n_1.
Qed.

Lemma nth_derive_cos_4n_2 : forall n, ⟦ Der^(4 * n + 2) ⟧ cos = (-cos)%function.
Proof.
  intros n. apply nth_derivative_imp_nth_derive. apply nth_derivative_cos_4n_2.
Qed.

Lemma nth_derive_cos_4n_3 : forall n, ⟦ Der^(4 * n + 3) ⟧ cos = sin.
Proof.
  intros n. apply nth_derivative_imp_nth_derive. apply nth_derivative_cos_4n_3.
Qed.

Lemma nth_derive_sin_4n_1 : forall n, ⟦ Der^(4 * n + 1) ⟧ sin = cos.
Proof.
  intros n. apply nth_derivative_imp_nth_derive. apply nth_derivative_sin_4n_1.
Qed.

Lemma nth_derive_sin_4n_2 : forall n, ⟦ Der^(4 * n + 2) ⟧ sin = (-sin)%function.
Proof.
  intros n. apply nth_derivative_imp_nth_derive. apply nth_derivative_sin_4n_2.
Qed.

Lemma nth_derive_sin_4n_3 : forall n, ⟦ Der^(4 * n + 3) ⟧ sin = (-cos)%function.
Proof.
  intros n. apply nth_derivative_imp_nth_derive. apply nth_derivative_sin_4n_3.
Qed.

Ltac step_nth_derive_trig :=
  first
    [ rewrite nth_derive_cos_4n
    | rewrite nth_derive_cos_4n_1
    | rewrite nth_derive_cos_4n_2
    | rewrite nth_derive_cos_4n_3
    | rewrite nth_derive_sin_4n
    | rewrite nth_derive_sin_4n_1
    | rewrite nth_derive_sin_4n_2
    | rewrite nth_derive_sin_4n_3
    | nat_mod4_normalize_derivative_only 
    ].


Ltac simplify_nth_derive_trig :=
  repeat step_nth_derive_trig.

Ltac finish_trig :=
  (repeat rewrite sin_0); (repeat rewrite cos_0); lra.

Lemma derive_0_cos_at_0 : 
  ⟦ Der^0 0 ⟧ cos = 1.
Proof.
  simplify_nth_derive_trig. finish_trig.
Qed.

Lemma derive_1_cos_at_0 : 
  ⟦ Der^1 0 ⟧ cos = 0.
Proof.
  simplify_nth_derive_trig. finish_trig.
Qed.

Lemma derive_2_cos_at_0 : 
  ⟦ Der^2 0 ⟧ cos = -1.
Proof.
  simplify_nth_derive_trig. finish_trig.
Qed.

Lemma derive_3_cos_at_0 : 
  ⟦ Der^3 0 ⟧ cos = 0.
Proof.
  simplify_nth_derive_trig. finish_trig. 
Qed.

Lemma derive_4_cos_at_0 : 
  ⟦ Der^4 0 ⟧ cos = 1.
Proof.
  simplify_nth_derive_trig. finish_trig.
Qed.

Lemma derive_5_cos_at_0 : 
  ⟦ Der^5 0 ⟧ cos = 0.
Proof.
  simplify_nth_derive_trig. finish_trig.
Qed.

Lemma derive_6_cos_at_0 : 
  ⟦ Der^6 0 ⟧ cos = -1.
Proof.
  simplify_nth_derive_trig. finish_trig.
Qed.

Lemma sin_pi_x_bounds : forall x, 0 < x < 1 -> 0 < sin (π * x) <= 1.
Proof.
  intros x H1.
  pose proof π_pos as H2.
  assert (H3 : 0 <= π * x <= π) by nra.
  split.
  - pose proof (sin_consistency_on_0_π (π * x) H3) as H4.
    rewrite H4.
    unfold sin_0_π.
    pose proof (cos_0_π_spec (π * x) H3) as H5.
    pose proof (cos_0_π_in_range (π * x) H3) as H6.
    assert (H7 : cos_0_π (π * x) <> 1).
    { intros H8. rewrite H8 in H5. rewrite A_at_1 in H5. nra. }
    assert (H8 : cos_0_π (π * x) <> -1).
    { intros H9. rewrite H9 in H5. rewrite A_at_neg_1 in H5. nra. }
    apply sqrt_lt_R0. solve_R.
  - pose proof (sin_bounds (π * x)) as H4.
    lra.
Qed.

Lemma tan_pi_div_4 : tan (π / 4) = 1.
Proof. 
  unfold tan. rewrite sin_π_over_4, cos_π_over_4. field.
  intros H1. apply Rmult_eq_compat_r with (r := sqrt 2) in H1.
  rewrite sqrt_def in H1; try lra.
Qed.

Lemma arctan_1 : arctan 1 = π / 4.
Proof.
  pose proof arctan_spec as [H1 [H2 [H3 H4]]].
  rewrite <- tan_pi_div_4.
  rewrite H3; auto.
  pose proof π_pos as H5. solve_R.
Qed.

Lemma arctan_neg : forall x, arctan (-x) = - arctan x.
Proof.
  intros x.
  pose proof arctan_spec as [H1 [H2 [H3 H4]]].
  assert (H5 : ⟦ der ⟧ (λ t : ℝ, cos (- t)) = (λ t : ℝ, sin (- t))).
  {
    intros t.
    pose proof derivative_at_comp (fun z => -z) cos (fun _ => -1) (fun z => -sin z) t as H6.
    assert (H7 : ⟦ der t ⟧ (fun z => -z) = (fun _ => -1)).
    {
      eapply derivative_at_ext_val.
      - apply derivative_at_eq with (f1 := fun z => -1 * z).
        + exists 1. split; [lra|]. intros z _. lra.
        + apply derivative_at_mult_const_l. apply derivative_at_id.
      - simpl. lra.
    }
    assert (H8 : ⟦ der (-t) ⟧ cos = (fun z => -sin z)).
    {
      eapply derivative_at_ext_val.
      - apply derivative_at_cos.
      - reflexivity.
    }
    specialize (H6 H7 H8).
    eapply derivative_at_ext_val.
    - apply derivative_at_eq with (f1 := compose cos (fun z => - z)).
      + exists 1. split; [lra|]. intros z _. reflexivity.
      + exact H6.
    - unfold compose. lra.
  }
  assert (H6 : ⟦ der ⟧ (λ t : ℝ, sin (- t)) = (λ t : ℝ, - cos (- t))).
  {
    intros t.
    pose proof derivative_at_comp (fun z => -z) sin (fun _ => -1) cos t as H7.
    assert (H8 : ⟦ der t ⟧ (fun z => -z) = (fun _ => -1)).
    {
      eapply derivative_at_ext_val.
      - apply derivative_at_eq with (f1 := fun z => -1 * z).
        + exists 1. split; [lra|]. intros z _. lra.
        + apply derivative_at_mult_const_l. apply derivative_at_id.
      - simpl. lra.
    }
    assert (H9 : ⟦ der (-t) ⟧ sin = cos).
    {
      eapply derivative_at_ext_val.
      - apply derivative_at_sin.
      - reflexivity.
    }
    specialize (H7 H8 H9).
    eapply derivative_at_ext_val.
    - apply derivative_at_eq with (f1 := compose sin (fun z => - z)).
      + exists 1. split; [lra|]. intros z _. reflexivity.
      + exact H7.
    - unfold compose. lra.
  }
  assert (H7 : forall z, cos (-z) = cos z).
  {
    intros z.
    pose proof theorem_4 (fun t => cos (-t)) (fun t => sin (-t)) (fun t => - cos (-t)) 1 0 as H8.
    specialize (H8 H5 H6).
    assert (H9 : forall t, - cos (- t) + cos (- t) = 0) by (intro t; lra).
    specialize (H8 H9).
    assert (H10 : cos (- 0) = 1) by (replace (-0) with 0 by lra; apply cos_0).
    assert (H11 : sin (- 0) = 0) by (replace (-0) with 0 by lra; apply sin_0).
    specialize (H8 H10 H11 z).
    rewrite H8. lra.
  }
  assert (H8 : ⟦ der ⟧ (λ t : ℝ, - cos (- t)) = (λ t : ℝ, - sin (- t))).
  {
    intros t.
    eapply derivative_at_ext_val.
    - apply derivative_at_eq with (f1 := fun z => -1 * cos (-z)).
      + exists 1. split; [lra|]. intros z _. lra.
      + apply derivative_at_mult_const_l. apply H5.
    - lra.
  }
  assert (H9 : forall z, sin (-z) = - sin z).
  {
    intros z.
    pose proof theorem_4 (fun t => sin (-t)) (fun t => - cos (-t)) (fun t => - sin (-t)) 0 (-1) as H10.
    specialize (H10 H6 H8).
    assert (H11 : forall t, - sin (- t) + sin (- t) = 0) by (intro t; lra).
    specialize (H10 H11).
    assert (H12 : sin (- 0) = 0) by (replace (-0) with 0 by lra; apply sin_0).
    assert (H13 : - cos (- 0) = -1) by (replace (-0) with 0 by lra; rewrite cos_0; lra).
    specialize (H10 H12 H13 z).
    rewrite H10. lra.
  }
  assert (H10 : forall z, tan (-z) = - tan z).
  {
    intros z. unfold tan. rewrite H7, H9.
    replace (- sin z / cos z) with (- (sin z / cos z)) by lra.
    reflexivity.
  }
  assert (H11 : arctan x ∈ (-(π/2), π/2)) by (apply H2; apply Full_intro).
  assert (H12 : - arctan x ∈ (-(π/2), π/2)).
  { destruct H11 as [H13 H14]; split; lra. }
  rewrite <- (H3 (- arctan x)); auto.
  f_equal.
  rewrite H10.
  assert (H13 : tan (arctan x) = x) by (apply H4; apply Full_intro).
  rewrite H13. reflexivity.
Qed.

Lemma problem_6_a : π / 4 = arctan (1/2) + arctan (1/3).
Proof.
  rewrite arctan_plus; try lra.
  - replace ((1 / 2 + 1 / 3) / (1 - 1 / 2 * (1 / 3))) with 1 by field.
    symmetry; apply arctan_1.
Qed.

Lemma problem_6_b : π / 4 = 4 * arctan (1/5) - arctan (1/239).
Proof.
  assert (2 * arctan (1/5) = arctan (5/12)) as H1.
  {
    replace (2 * arctan (1/5)) with (arctan (1/5) + arctan (1/5)) by lra.
    rewrite arctan_plus; try lra.
    f_equal; field.
  }
  assert (4 * arctan (1/5) = arctan (120/119)) as H2.
  {
    replace (4 * arctan (1/5)) with (2 * arctan (1/5) + 2 * arctan (1/5)) by lra.
    rewrite H1.
    rewrite arctan_plus; try lra. f_equal; field.
  }
  rewrite H2.
  replace (arctan (120/119) - arctan (1/239)) with (arctan (120/119) + arctan (-(1/239))).
  2: { rewrite arctan_neg; lra. }
  rewrite arctan_plus; try lra.
  - replace ((120 / 119 + -(1 / 239)) / (1 - 120 / 119 * -(1 / 239))) with 1 by field.
    symmetry; apply arctan_1.
Qed.

Lemma derivative_at_arcsin : forall x, -1 < x < 1 -> ⟦ der x ⟧ arcsin = (fun x => 1 / sqrt (1 - x ^ 2)).
Proof.
  intros x H1.
  assert (H2 : -(π/2) < π/2) by (pose proof π_pos as H2; lra).
  assert (H3 : continuous_on sin [-(π/2), π/2]).
  { apply continuous_imp_continuous_on. apply continuous_sin. }
  assert (H4 : one_to_one_on sin [-(π/2), π/2]).
  { apply increasing_on_imp_one_to_one_on. apply sin_increasing_on. }
  assert (H5 : sin (π / 2) = 1) by apply sin_π_over_2.
  assert (H6 : sin (- (π / 2)) = -1).
  {
    rewrite <- sin_periodic.
    replace (- (π / 2) + 2 * π) with (3 * π / 2) by lra.
    apply sin_3_π_over_2.
  }
  assert (H7 : inverse_on sin arcsin [-(π/2), π/2] [Rmin (sin (- (π / 2))) (sin (π / 2)), Rmax (sin (- (π / 2))) (sin (π / 2))]).
  {
    rewrite H5, H6.
    replace (Rmin (-1) 1) with (-1) by solve_R.
    replace (Rmax (-1) 1) with 1 by solve_R.
    apply arcsin_spec.
  }
  assert (H8 : x ∈ (Rmin (sin (- (π / 2))) (sin (π / 2)), Rmax (sin (- (π / 2))) (sin (π / 2)))).
  { rewrite H5, H6. solve_R. }
  assert (H9 : ⟦ der ⟧ sin (-(π/2), π/2) = cos).
  { intros y H9. left. split; [auto_interval |]. apply derivative_at_sin. }
  assert (H10 : forall z, -(π/2) < z < π/2 -> cos z > 0).
  {
    intros z H10. pose proof π_pos as H11.
    assert (0 < z < π / 2 \/ z = 0 \/ - (π / 2) < z < 0) as [H12 | [H12 | H12]] by lra.
    - assert (H13 : z ∈ [0, π]) by (split; lra).
      assert (H14 : π / 2 ∈ [0, π]) by (split; lra).
      pose proof cos_decreasing_on z (π / 2) H13 H14 ltac:(lra) as H15.
      rewrite cos_π_over_2 in H15. lra.
    - subst z. rewrite cos_0. lra.
    - assert (H13 : cos z = cos (z + 2 * π)). { symmetry. apply cos_periodic. } rewrite H13.
      assert (H14 : π < z + 2 * π < 2 * π) by lra. rewrite cos_on_π_2π; try lra. replace (2 * π - (z + 2 * π)) with (- z) by lra.
      assert (H15 : cos_0_π (-z) <= 0 \/ cos_0_π (-z) > 0) by lra. destruct H15 as [H15 | H15]; try lra.
      assert (H16 : cos_0_π (-z) = 0 \/ cos_0_π (-z) < 0) by lra. destruct H16 as [H16 | H16].
      + pose proof cos_0_π_spec (-z) as H17. assert (0 <= -z <= π) as H18 by lra. specialize (H17 H18). rewrite H16 in H17. rewrite A_at_0 in H17. lra.
      + assert (H17 : cos_0_π (-z) ∈ [-1, 1]). { apply cos_0_π_in_range; lra. }
        assert (H18 : 0 ∈ [-1, 1]) by (split; lra).
        pose proof A_decreases (cos_0_π (-z)) 0 H17 H18 H16 as H19.
        pose proof cos_0_π_spec (-z) as H20. assert (0 <= -z <= π) as H21 by lra. specialize (H20 H21).
        rewrite H20 in H19. rewrite A_at_0 in H19. lra.
  }
  assert (H11 : arcsin x ∈ (-(π/2), π/2)).
  {
    pose proof arcsin_spec as [H11a [H11b [H11c H11d]]].
    assert (H12 : arcsin x ∈ [-(π/2), π/2]) by (apply H11b; solve_R).
    destruct H12 as [H12 H13].
    assert (arcsin x = -(π/2) \/ arcsin x = π/2 \/ -(π/2) < arcsin x < π/2) as [H14 | [H14 | H14]] by lra.
    - assert (H15 : sin (arcsin x) = x) by (apply H11d; solve_R).
      rewrite H14 in H15. rewrite H6 in H15. lra.
    - assert (H15 : sin (arcsin x) = x) by (apply H11d; solve_R).
      rewrite H14 in H15. rewrite H5 in H15. lra.
    - exact H14.
  }
  assert (H12 : cos (arcsin x) <> 0).
  { pose proof H10 (arcsin x) H11 as H12. lra. }
  pose proof (theorem_12_5 sin arcsin cos (-(π/2)) (π/2) x H2 H3 H4 H7 H8 H9 H12) as H13.
  eapply derivative_at_ext_val.
  - exact H13.
  - simpl.
    assert (H14 : cos (arcsin x) > 0) by (apply H10; exact H11).
    assert (H15 : (cos (arcsin x))^2 = 1 - x^2).
    {
      pose proof pythagorean_identity (arcsin x) as H15.
      pose proof arcsin_spec as [H16 [H17 [H18 H19]]].
      assert (H20 : sin (arcsin x) = x) by (apply H19; solve_R).
      rewrite H20 in H15. lra.
    }
    assert (H16 : cos (arcsin x) * cos (arcsin x) = sqrt (1 - x^2) * sqrt (1 - x^2)).
    {
      replace (cos (arcsin x) * cos (arcsin x)) with (cos (arcsin x) ^ 2) by nra.
      replace (sqrt (1 - x^2) * sqrt (1 - x^2)) with (sqrt (1 - x^2) ^ 2) by nra.
      rewrite pow2_sqrt; solve_R.
    }
    assert (H17 : cos (arcsin x) = sqrt (1 - x^2) \/ cos (arcsin x) = - sqrt (1 - x^2)) by nra.
    assert (H18 : sqrt (1 - x^2) > 0).
    { apply sqrt_lt_R0. solve_R. }
    destruct H17 as [H17 | H17]; [| lra].
    rewrite H17. unfold Rdiv. rewrite Rmult_1_l. simpl. auto.
Qed.

Lemma derivative_at_arccos : forall x, -1 < x < 1 -> ⟦ der x ⟧ arccos = (fun x => - 1 / sqrt (1 - x ^ 2)).
Proof.
  intros x H1.
  assert (H2 : 0 < π) by apply π_pos.
  assert (H3 : continuous_on cos [0, π]).
  { apply continuous_imp_continuous_on. apply continuous_cos. }
  assert (H4 : one_to_one_on cos [0, π]).
  { apply decreasing_on_imp_one_to_one_on. apply cos_decreasing_on. }
  assert (H5 : cos 0 = 1) by apply cos_0.
  assert (H6 : cos π = -1) by apply cos_π.
  assert (H7 : inverse_on cos arccos [0, π] [Rmin (cos 0) (cos π), Rmax (cos 0) (cos π)]).
  {
    rewrite H5, H6.
    replace (Rmin 1 (-1)) with (-1) by solve_R.
    replace (Rmax 1 (-1)) with 1 by solve_R.
    apply arccos_spec.
  }
  assert (H8 : x ∈ (Rmin (cos 0) (cos π), Rmax (cos 0) (cos π))).
  { rewrite H5, H6. solve_R. }
  assert (H9 : ⟦ der ⟧ cos (0, π) = (- sin)%function).
  { intros y H9. left. split; [auto_interval |]. apply derivative_at_cos. }
  assert (H10 : forall z, 0 < z < π -> - sin z <> 0).
  {
    intros z H10.
    assert (H11 : sin z = sin_0_π z) by (apply sin_consistency_on_0_π; lra).
    rewrite H11. unfold sin_0_π.
    assert (H12 : cos_0_π z ∈ [-1, 1]) by (apply cos_0_π_in_range; lra).
    assert (H13 : cos_0_π z <> 1).
    { intros H13. pose proof cos_0_π_spec z ltac:(lra) as H14. rewrite H13 in H14. rewrite A_at_1 in H14. lra. }
    assert (H14 : cos_0_π z <> -1).
    { intros H14. pose proof cos_0_π_spec z ltac:(lra) as H15. rewrite H14 in H15. rewrite A_at_neg_1 in H15. lra. }
    assert (H15 : 1 - cos_0_π z ^ 2 > 0). { destruct H12 as [H12a H12b]. nra. }
    pose proof sqrt_lt_R0 (1 - cos_0_π z ^ 2) H15 as H16.
    lra.
  }
  assert (H11 : arccos x ∈ (0, π)).
  {
    pose proof arccos_spec as [H11a [H11b [H11c H11d]]].
    assert (H12 : arccos x ∈ [0, π]) by (apply H11b; solve_R).
    destruct H12 as [H12 H13].
    assert (arccos x = 0 \/ arccos x = π \/ 0 < arccos x < π) as [H14 | [H14 | H14]] by lra.
    - assert (H15 : cos (arccos x) = x) by (apply H11d; solve_R).
      rewrite H14 in H15. rewrite H5 in H15. lra.
    - assert (H15 : cos (arccos x) = x) by (apply H11d; solve_R).
      rewrite H14 in H15. rewrite H6 in H15. lra.
    - exact H14.
  }
  assert (H12 : - sin (arccos x) <> 0).
  { apply H10. exact H11. }
  pose proof (theorem_12_5 cos arccos (- sin)%function 0 π x H2 H3 H4 H7 H8 H9 H12) as H13.
  eapply derivative_at_ext_val.
  - exact H13.
  - simpl.
    assert (H14 : sin (arccos x) > 0).
    {
      assert (H14 : sin (arccos x) = sin_0_π (arccos x)) by (apply sin_consistency_on_0_π; solve_R).
      rewrite H14. unfold sin_0_π.
      assert (H15 : cos_0_π (arccos x) ∈ [-1, 1]) by (apply cos_0_π_in_range; solve_R).
      assert (H16 : cos_0_π (arccos x) <> 1).
      { intros H16. pose proof cos_0_π_spec (arccos x) ltac:(solve_R) as H17. rewrite H16 in H17. rewrite A_at_1 in H17. solve_R. }
      assert (H17 : cos_0_π (arccos x) <> -1).
      { intros H17. pose proof cos_0_π_spec (arccos x) ltac:(solve_R) as H18. rewrite H17 in H18. rewrite A_at_neg_1 in H18. solve_R. }
      assert (H18 : 1 - cos_0_π (arccos x) ^ 2 > 0) by (destruct H15; nra).
      apply sqrt_lt_R0. exact H18.
    }
    assert (H15 : (sin (arccos x))^2 = 1 - x^2).
    {
      pose proof pythagorean_identity (arccos x) as H15.
      pose proof arccos_spec as [H16 [H17 [H18 H19]]].
      assert (H20 : cos (arccos x) = x) by (apply H19; solve_R).
      rewrite H20 in H15. lra.
    }
    assert (H16 : sin (arccos x) * sin (arccos x) = sqrt (1 - x^2) * sqrt (1 - x^2)).
    {
      replace (sin (arccos x) * sin (arccos x)) with (sin (arccos x) ^ 2) by nra.
      replace (sqrt (1 - x^2) * sqrt (1 - x^2)) with (sqrt (1 - x^2) ^ 2) by nra.
      rewrite pow2_sqrt; solve_R.
    }
    assert (H17 : sin (arccos x) = sqrt (1 - x^2) \/ sin (arccos x) = - sqrt (1 - x^2)) by nra.
    assert (H18 : sqrt (1 - x^2) > 0).
    { apply sqrt_lt_R0. solve_R. }
    destruct H17 as [H17 | H17]; [| lra].
    rewrite H17. replace (1 - x * (x * 1)) with (1 - x^2) by lra. 
    unfold Rdiv. field. lra.
Qed.

Lemma derivative_arctan : ⟦ der ⟧ arctan = (fun x => 1 / (1 + x ^ 2)).
Proof.
  intros x.
  assert (H1 : -(π/2) < π/2) by (pose proof π_pos; lra).
  pose proof arctan_spec as [S1 [S2 [S3 S4]]].
  assert (H2 : arctan x ∈ (-(π/2), π/2)) by (apply S2; apply Full_intro).
  destruct H2 as [H2a H2b].
  set (a := (-(π/2) + arctan x) / 2).
  set (b := (π/2 + arctan x) / 2).
  assert (H3 : -(π/2) < a) by (unfold a; lra).
  assert (H4 : a < arctan x) by (unfold a; lra).
  assert (H5 : arctan x < b) by (unfold b; lra).
  assert (H6 : b < π/2) by (unfold b; lra).
  assert (H7 : a < b) by lra.
  assert (H8 : continuous_on tan [a, b]).
  {
    apply continuous_on_subset with (A2 := (-(π/2), π/2)).
    - intros z Hz. solve_R.
    - replace (- (π / 2)) with (- π / 2) by lra; apply continuous_on_tan.
  }
  assert (H9 : one_to_one_on tan [a, b]).
  {
    apply increasing_on_imp_one_to_one_on.
    intros z1 z2 Hz1 Hz2 Hz3. apply tan_increasing_on; solve_R.
  }
  assert (H10 : inverse_on tan arctan [a, b] [Rmin (tan a) (tan b), Rmax (tan a) (tan b)]).
  {
    assert (H10a : tan a < tan b) by (apply tan_increasing_on; solve_R).
    rewrite Rmin_left by lra. rewrite Rmax_right by lra.
    split; [| split; [| split]].
    - intros z Hz.
      assert (H10b : a = z \/ a < z) by solve_R.
      assert (H10c : z = b \/ z < b) by solve_R.
      split.
      + destruct H10b as [H10b | H10b]; [rewrite H10b; lra | apply Rlt_le; apply tan_increasing_on; solve_R].
      + destruct H10c as [H10c | H10c]; [rewrite H10c; lra | apply Rlt_le; apply tan_increasing_on; solve_R].
    - intros z Hz.
      destruct Hz as [Hz1 Hz2].
      assert (H10b : arctan z ∈ (-(π/2), π/2)) by (apply S2; apply Full_intro).
      assert (H10c : a <= arctan z \/ arctan z < a) by lra.
      destruct H10c as [H10c | H10c].
      + assert (H10d : arctan z <= b \/ b < arctan z) by lra.
        destruct H10d as [H10d | H10d]; [split; auto |].
        * assert (H10e : tan b < tan (arctan z)).
          { apply tan_increasing_on; solve_R. }
          rewrite S4 in H10e; [lra | apply Full_intro].
      + assert (H10e : tan (arctan z) < tan a).
        { apply tan_increasing_on; solve_R. }
        rewrite S4 in H10e; [lra | apply Full_intro].
    - intros z Hz. apply S3. solve_R.
    - intros z Hz. apply S4. apply Full_intro.
  }
  assert (H11 : x ∈ (Rmin (tan a) (tan b), Rmax (tan a) (tan b))).
  {
    assert (H11a : tan a < tan b) by (apply tan_increasing_on; solve_R).
    rewrite Rmin_left by lra. rewrite Rmax_right by lra.
    assert (H11b : tan a < x).
    {
      assert (H11c : tan a < tan (arctan x)).
      { apply tan_increasing_on; solve_R. }
      rewrite S4 in H11c; [exact H11c | apply Full_intro].
    }
    assert (H11c : x < tan b).
    {
      assert (H11d : tan (arctan x) < tan b).
      { apply tan_increasing_on; solve_R. }
      rewrite S4 in H11d; [exact H11d | apply Full_intro].
    }
    split; auto.
  }
  assert (H12 : forall z, -(π/2) < z < π/2 -> cos z > 0).
  {
    intros z Hz. pose proof π_pos as H13.
    assert (0 < z < π / 2 \/ z = 0 \/ - (π / 2) < z < 0) as [Hz1 | [Hz1 | Hz1]] by lra.
    - assert (Hz2 : z ∈ [0, π]) by (split; lra).
      assert (Hz3 : π / 2 ∈ [0, π]) by (split; lra).
      pose proof cos_decreasing_on z (π / 2) Hz2 Hz3 ltac:(lra) as Hz4.
      rewrite cos_π_over_2 in Hz4. lra.
    - subst z. rewrite cos_0. lra.
    - assert (Hz2 : cos z = cos (z + 2 * π)). { symmetry. apply cos_periodic. } rewrite Hz2.
      assert (Hz3 : π < z + 2 * π < 2 * π) by lra. rewrite cos_on_π_2π; try lra. replace (2 * π - (z + 2 * π)) with (- z) by lra.
      assert (Hz4 : cos_0_π (-z) <= 0 \/ cos_0_π (-z) > 0) by lra. destruct Hz4 as [Hz4 | Hz4]; try lra.
      assert (Hz5 : cos_0_π (-z) = 0 \/ cos_0_π (-z) < 0) by lra. destruct Hz5 as [Hz5 | Hz5].
      + pose proof cos_0_π_spec (-z) as Hz6. assert (0 <= -z <= π) as Hz7 by lra. specialize (Hz6 Hz7). rewrite Hz5 in Hz6. rewrite A_at_0 in Hz6. lra.
      + assert (Hz6 : cos_0_π (-z) ∈ [-1, 1]). { apply cos_0_π_in_range; lra. }
        assert (Hz7 : 0 ∈ [-1, 1]) by (split; lra).
        pose proof A_decreases (cos_0_π (-z)) 0 Hz6 Hz7 Hz5 as Hz8.
        pose proof cos_0_π_spec (-z) as Hz9. assert (0 <= -z <= π) as Hz10 by lra. specialize (Hz9 Hz10).
        rewrite Hz9 in Hz8. rewrite A_at_0 in Hz8. lra.
  }
  assert (H13 : ⟦ der ⟧ tan (a, b) = (sec ^ 2)%function).
  {
    intros y Hy. left. split; [auto_interval |].
    apply derivative_at_tan.
    intro H13a.
    assert (H13b : cos y > 0) by (apply H12; solve_R).
    lra.
  }
  assert (H14 : (sec ^ 2)%function (arctan x) <> 0).
  {
    intro H14a.
    assert (H14b : sec (arctan x) ^ 2 = 0) by (exact H14a).
    unfold sec in H14b.
    assert (H14c : cos (arctan x) > 0) by (apply H12; solve_R).
    assert (H14d : 1 / cos (arctan x) = 0) by nra.
    assert (H14e : 1 / cos (arctan x) * cos (arctan x) = 0 * cos (arctan x)) by (f_equal; lra).
    assert (H14f : 1 / cos (arctan x) * cos (arctan x) = 1) by (field; lra).
    lra.
  }
  pose proof (theorem_12_5 tan arctan (sec ^ 2)%function a b x H7 H8 H9 H10 H11 H13 H14) as H15.
  eapply derivative_at_ext_val.
  - exact H15.
  - simpl. unfold sec.
    assert (H16 : cos (arctan x) > 0) by (apply H12; solve_R).
    replace (/ (1 / cos (arctan x) * (1 / cos (arctan x) * 1))) with (cos (arctan x) ^ 2) by (field; lra).
    replace (x * (x * 1)) with (x ^ 2) by ring.
    pose proof pythagorean_identity (arctan x) as H17.
    assert (H18 : tan (arctan x) = x) by (apply S4; apply Full_intro).
    unfold tan in H18.
    assert (H19 : sin (arctan x) = x * cos (arctan x)).
    { replace (sin (arctan x)) with (sin (arctan x) / cos (arctan x) * cos (arctan x)) by (field; lra). rewrite H18. reflexivity. }
    rewrite H19 in H17.
    replace ((x * cos (arctan x)) ^ 2 + cos (arctan x) ^ 2) with (cos (arctan x) ^ 2 * (x ^ 2 + 1)) in H17 by ring.
    apply Rmult_eq_reg_r with (r := x ^ 2 + 1); [| nra]. solve_R.
Qed.

Lemma arctan_0 : arctan 0 = 0.
Proof.
  pose proof arctan_spec as [H1 [H2 [H3 H4]]].
  rewrite <- H3; auto. rewrite tan_0; auto.
  pose proof π_pos as H5. solve_R.
Qed.

Lemma csc_identity : forall (θ : ℝ),
  sin θ <> 0 -> csc θ = 1 / sin θ.
Proof.
  intros θ H1. unfold csc. reflexivity.
Qed.

Lemma sec_identity : forall (θ : ℝ),
  cos θ <> 0 -> sec θ = 1 / cos θ.
Proof.
  intros θ H1. unfold sec. reflexivity.
Qed.

Lemma tan_identity : forall (θ : ℝ),
  cos θ <> 0 -> tan θ = sin θ / cos θ.
Proof.
  intros θ H1. unfold tan. reflexivity.
Qed.

Lemma cot_identity : forall (θ : ℝ),
  sin θ <> 0 -> cot θ = cos θ / sin θ.
Proof.
  intros θ H1. unfold cot, tan.
  assert (cos θ = 0 \/ cos θ <> 0) as [H2 | H2] by lra.
  - unfold Rdiv. rewrite H2, Rinv_0, Rmult_0_r, Rinv_0, Rmult_0_l. lra.
  - field. split; lra.
Qed.

Lemma cot_tan_identity : forall (θ : ℝ),
  tan θ <> 0 -> cot θ = 1 / tan θ.
Proof.
  intros θ H1. unfold cot. reflexivity.
Qed.

Lemma tan_sec_identity : forall (θ : ℝ),
  cos θ <> 0 -> 1 + (tan θ)^2 = (sec θ)^2.
Proof.
  intros θ H1. unfold tan, sec.
  pose proof (Trigonometry.pythagorean_identity θ) as H2.
  cut (1 + (sin θ / cos θ) ^ 2 = (sin θ ^ 2 + cos θ ^ 2) / cos θ ^ 2).
  - intros H3. rewrite H3. rewrite H2. field. lra.
  - field. lra.
Qed.

Lemma cot_csc_identity : forall (θ : ℝ),
  sin θ <> 0 -> 1 + (cot θ)^2 = (csc θ)^2.
Proof.
  intros θ H1. unfold cot, csc, tan.
  assert (cos θ = 0 \/ cos θ <> 0) as [H2 | H2] by lra.
  - unfold Rdiv. rewrite H2, Rinv_0, Rmult_0_r, Rinv_0, Rmult_0_r.
    pose proof (Trigonometry.pythagorean_identity θ) as H3. rewrite H2 in H3.
    replace (0^2) with 0 in H3 by lra.
    replace (0^2) with 0 by lra.
    replace ((1 * / sin θ) ^ 2) with (1 / (sin θ) ^ 2) by (unfold Rdiv; field; assumption).
    assert (sin θ ^ 2 = 1) as H4 by lra.
    rewrite H4. unfold Rdiv. rewrite Rinv_1. lra.
  - pose proof (Trigonometry.pythagorean_identity θ) as H3.
    cut (1 + (1 / (sin θ / cos θ)) ^ 2 = (sin θ ^ 2 + cos θ ^ 2) / sin θ ^ 2).
    + intros H4. rewrite H4. rewrite H3. field. lra.
    + field. split; lra.
Qed.

Lemma sin_even_odd : forall (θ : ℝ),
  sin (- θ) = - sin θ.
Proof.
  intros θ.
  pose proof (Trigonometry.sin_plus θ (-θ)) as H1.
  assert (θ + - θ = 0) as H2 by lra.
  rewrite H2 in H1.
  rewrite Trigonometry.sin_0 in H1.
  pose proof (Trigonometry.cos_plus θ (-θ)) as H3.
  rewrite H2 in H3.
  rewrite Trigonometry.cos_0 in H3.
  pose proof (Trigonometry.pythagorean_identity θ) as H4.
  assert (- sin (- θ) = sin θ * (cos θ * cos (-θ) - sin θ * sin (-θ)) - cos θ * (sin θ * cos (-θ) + cos θ * sin (-θ)) + sin (- θ) * (sin θ ^ 2 + cos θ ^ 2 - 1)) as H5 by lra.
  rewrite <- H3 in H5.
  rewrite <- H1 in H5.
  rewrite H4 in H5.
  lra.
Qed.

Lemma cos_even_odd : forall (θ : ℝ),
  cos (- θ) = cos θ.
Proof.
  intros θ.
  pose proof (Trigonometry.sin_plus θ (-θ)) as H1.
  assert (θ + - θ = 0) as H2 by lra.
  rewrite H2 in H1.
  rewrite Trigonometry.sin_0 in H1.
  pose proof (Trigonometry.cos_plus θ (-θ)) as H3.
  rewrite H2 in H3.
  rewrite Trigonometry.cos_0 in H3.
  pose proof (Trigonometry.pythagorean_identity θ) as H4.
  assert (cos (-θ) = cos θ * (cos θ * cos (-θ) - sin θ * sin (-θ)) + sin θ * (sin θ * cos (-θ) + cos θ * sin (-θ)) - cos (-θ) * (sin θ ^ 2 + cos θ ^ 2 - 1)) as H5 by lra.
  rewrite <- H3 in H5.
  rewrite <- H1 in H5.
  rewrite H4 in H5.
  lra.
Qed.

Lemma tan_even_odd : forall (θ : ℝ),
  cos θ <> 0 -> tan (- θ) = - tan θ.
Proof.
  intros θ H1. unfold tan. rewrite sin_even_odd, cos_even_odd.
  field. assumption.
Qed.

Lemma sin_shift : forall (θ : ℝ),
  sin (π / 2 - θ) = cos θ.
Proof.
  intros θ.
  assert (π / 2 - θ = π / 2 + -θ) as H1 by lra.
  rewrite H1.
  rewrite Trigonometry.sin_plus.
  rewrite sin_even_odd.
  rewrite cos_even_odd.
  rewrite Trigonometry.sin_π_over_2.
  rewrite Trigonometry.cos_π_over_2.
  lra.
Qed.

Lemma cos_shift : forall (θ : ℝ),
  cos (π / 2 - θ) = sin θ.
Proof.
  intros θ.
  assert (π / 2 - θ = π / 2 + -θ) as H1 by lra.
  rewrite H1.
  rewrite Trigonometry.cos_plus.
  rewrite sin_even_odd.
  rewrite cos_even_odd.
  rewrite Trigonometry.sin_π_over_2.
  rewrite Trigonometry.cos_π_over_2.
  lra.
Qed.

Lemma tan_shift : forall (θ : ℝ),
  cos θ <> 0 -> sin θ <> 0 -> tan (π / 2 - θ) = cot θ.
Proof.
  intros θ H1 H2. unfold tan, cot.
  rewrite sin_shift, cos_shift.
  unfold tan. solve_R.
Qed.

Lemma sin_minus : forall x y : ℝ,
  sin (x - y) = sin x * cos y - cos x * sin y.
Proof.
  intros x y.
  assert (x - y = x + -y) as H1 by lra.
  rewrite H1.
  rewrite Trigonometry.sin_plus.
  rewrite sin_even_odd, cos_even_odd.
  lra.
Qed.

Lemma cos_minus : forall x y : ℝ,
  cos (x - y) = cos x * cos y + sin x * sin y.
Proof.
  intros x y.
  assert (x - y = x + -y) as H1 by lra.
  rewrite H1.
  rewrite Trigonometry.cos_plus.
  rewrite sin_even_odd, cos_even_odd.
  lra.
Qed.

Lemma tan_minus : forall x y : ℝ,
  cos (x - y) <> 0 -> cos x <> 0 -> cos y <> 0 -> 1 + tan x * tan y <> 0 ->
  tan (x - y) = (tan x - tan y) / (1 + tan x * tan y).
Proof.
  intros x y H1 H2 H3 H4. unfold tan. rewrite sin_minus, cos_minus.
  replace (sin x * cos y - cos x * sin y) with ((sin x / cos x - sin y / cos y) * (cos x * cos y)).
  - replace (cos x * cos y + sin x * sin y) with ((1 + (sin x / cos x) * (sin y / cos y)) * (cos x * cos y)).
    + field; repeat split; auto. rewrite <- cos_minus. exact H1.
    + field; split; assumption.
  - field; split; assumption.
Qed.

Lemma sin_2x : forall x : ℝ,
  sin (2 * x) = 2 * sin x * cos x.
Proof.
  intros x.
  assert (2 * x = x + x) as H1 by lra.
  rewrite H1.
  rewrite sin_plus.
  lra.
Qed.

Lemma cos_2x_1 : forall x : ℝ,
  cos (2 * x) = (cos x)^2 - (sin x)^2.
Proof.
  intros x.
  assert (2 * x = x + x) as H1 by lra.
  rewrite H1.
  rewrite cos_plus.
  lra.
Qed.

Lemma cos_2x_2 : forall x : ℝ,
  cos (2 * x) = 2 * (cos x)^2 - 1.
Proof.
  intros x. rewrite cos_2x_1.
  pose proof (Trigonometry.pythagorean_identity x) as H1.
  lra.
Qed.

Lemma cos_2x_3 : forall x : ℝ,
  cos (2 * x) = 1 - 2 * (sin x)^2.
Proof.
  intros x. rewrite cos_2x_1.
  pose proof (Trigonometry.pythagorean_identity x) as H1.
  lra.
Qed.

Lemma tan_2x : forall x : ℝ,
  cos (2 * x) <> 0 -> cos x <> 0 -> 1 - (tan x)^2 <> 0 ->
  tan (2 * x) = (2 * tan x) / (1 - (tan x)^2).
Proof.
  intros x H1 H2 H3. unfold tan. rewrite sin_2x, cos_2x_1.
  replace (2 * sin x * cos x) with ((2 * (sin x / cos x)) * (cos x)^2).
  - replace ((cos x) ^ 2 - (sin x) ^ 2) with ((1 - (sin x / cos x)^2) * (cos x)^2).
    + field; repeat split; auto. rewrite <- cos_2x_1. exact H1.
    + field; repeat split; auto.
  - field; repeat split; auto.
Qed.

Lemma half_angle_sin : forall x : ℝ,
  (sin x)^2 = (1 - cos (2 * x)) / 2.
Proof.
  intros x. rewrite cos_2x_1.
  pose proof (Trigonometry.pythagorean_identity x) as H1.
  lra.
Qed.

Lemma half_angle_cos : forall x : ℝ,
  (cos x)^2 = (1 + cos (2 * x)) / 2.
Proof.
  intros x. rewrite cos_2x_1.
  pose proof (Trigonometry.pythagorean_identity x) as H1.
  lra.
Qed.

Lemma sin_pi_6 : sin (π / 6) = 1 / 2.
Proof.
  pose proof (Trigonometry.sin_π_over_2) as H1.
  assert (π / 2 = π / 6 + (π / 6 + π / 6)) as H2 by lra.
  rewrite H2 in H1.
  rewrite Trigonometry.sin_plus in H1.
  rewrite Trigonometry.sin_plus in H1.
  rewrite Trigonometry.cos_plus in H1.
  pose proof (Trigonometry.pythagorean_identity (π / 6)) as H3.
  assert (cos (π / 6) ^ 2 = 1 - sin (π / 6) ^ 2) as H4 by lra.
  assert (3 * sin (π / 6) - 4 * sin (π / 6) ^ 3 = 1) as H5.
  {
    replace (cos (π / 6) * cos (π / 6)) with (cos (π / 6) ^ 2) in H1 by lra.
    replace (sin (π / 6) * sin (π / 6)) with (sin (π / 6) ^ 2) in H1 by lra.
    replace (cos (π / 6) * (sin (π / 6) * cos (π / 6) + cos (π / 6) * sin (π / 6))) with (2 * cos (π / 6) ^ 2 * sin (π / 6)) in H1 by lra.
    rewrite H4 in H1.
    lra.
  }
  assert ((sin (π / 6) - 1 / 2) ^ 2 * (sin (π / 6) + 1) = 0) as H6.
  {
    replace ((sin (π / 6) - 1 / 2) ^ 2 * (sin (π / 6) + 1)) with ((1 - (3 * sin (π / 6) - 4 * sin (π / 6) ^ 3)) / 4) by lra.
    rewrite H5.
    lra.
  }
  assert (0 < π / 6 < π / 2) as H7 by (pose proof Trigonometry.π_pos; lra).
  pose proof (Trigonometry.sin_increasing_on 0 (π / 6)) as H8.
  assert (sin 0 < sin (π / 6)) as H9.
  {
    apply H8; try split; lra.
  }
  rewrite Trigonometry.sin_0 in H9.
  assert (sin (π / 6) = 1/2 \/ sin (π / 6) = -1) as [H10 | H10].
  {
    apply Rmult_integral in H6.
    destruct H6 as [H11 | H11].
    - left.
      replace (sin (π / 6)) with (sin (π / 6) - 1/2 + 1/2) by lra.
      assert (sin (π / 6) - 1/2 = 0) as H12 by nra.
      rewrite H12. lra.
    - right. nra.
  }
  - lra.
  - lra.
Qed.

Lemma cos_pi_6 : cos (π / 6) = √(3) / 2.
Proof.
  assert (0 <= cos (π / 6)) as H1.
  { apply Trigonometry.cos_sign_q1. pose proof Trigonometry.π_pos; split; lra. }
  assert (cos (π / 6) ^ 2 = 3 / 4) as H2.
  {
    pose proof (Trigonometry.pythagorean_identity (π / 6)) as H3.
    rewrite sin_pi_6 in H3.
    lra.
  }
  assert (cos (π / 6) = √(3) / 2 \/ cos (π / 6) = - (√(3) / 2)) as [H3 | H3].
  {
    assert (√(3)*√(3) = 3) as H4 by (apply sqrt_def; lra).
    assert ((cos (π / 6) - √(3) / 2) * (cos (π / 6) + √(3) / 2) = 0) as H5.
    {
      replace ((cos (π / 6) - √(3) / 2) * (cos (π / 6) + √(3) / 2)) with (cos (π / 6) * cos (π / 6) - (√(3) * √(3)) / 4) by lra.
      replace (cos (π / 6) * cos (π / 6)) with (cos (π / 6) ^ 2) by lra.
      lra.
    }
    apply Rmult_integral in H5. destruct H5 as [H6 | H6]; [left|right]; lra.
  }
  - lra.
  - assert (0 < √(3)) as H4 by (apply sqrt_lt_R0; lra). lra.
Qed.

Lemma tan_pi_6 : tan (π / 6) = √(3) / 3.
Proof.
  unfold tan. rewrite sin_pi_6, cos_pi_6.
  assert (√(3) * √(3) = 3) as H1 by (apply sqrt_def; lra).
  assert (√(3) <> 0) as H2 by (pose proof (sqrt_lt_R0 3); lra).
  unfold Rdiv.
  apply Rmult_eq_reg_r with (r := √(3)); try lra.
  assert (1 * / 2 * / (√(3) * / 2) * √(3) = 1) as H3 by (field; lra).
  rewrite H3.
  assert (√(3) * / 3 * √(3) = 1) as H4 by (replace (√(3) * / 3 * √(3)) with (√(3) * √(3) * / 3) by lra; rewrite H1; lra).
  rewrite H4.
  reflexivity.
Qed.

Lemma sin_pi_4 : sin (π / 4) = √(2) / 2.
Proof.
  apply Trigonometry.sin_π_over_4.
Qed.

Lemma cos_pi_4 : cos (π / 4) = √(2) / 2.
Proof.
  apply Trigonometry.cos_π_over_4.
Qed.

Lemma tan_pi_4 : tan (π / 4) = 1.
Proof.
  unfold tan. rewrite sin_pi_4, cos_pi_4.
  assert (0 < √(2)) as H1 by (apply sqrt_lt_R0; lra).
  assert (√(2) <> 0) as H2 by lra.
  field. repeat split; lra.
Qed.

Lemma sin_pi_3 : sin (π / 3) = √(3) / 2.
Proof.
  assert (π / 3 = π / 2 - π / 6) as H1 by lra.
  rewrite H1.
  rewrite sin_shift.
  apply cos_pi_6.
Qed.

Lemma cos_pi_3 : cos (π / 3) = 1 / 2.
Proof.
  assert (π / 3 = π / 2 - π / 6) as H1 by lra.
  rewrite H1.
  rewrite cos_shift.
  apply sin_pi_6.
Qed.

Lemma tan_pi_3 : tan (π / 3) = √(3).
Proof.
  unfold tan. rewrite sin_pi_3, cos_pi_3.
  unfold Rdiv. lra.
Qed.

Lemma sin_pi_2 : sin (π / 2) = 1.
Proof.
  apply Trigonometry.sin_π_over_2.
Qed.

Lemma cos_pi_2_val : cos (π / 2) = 0.
Proof.
  apply Trigonometry.cos_π_over_2.
Qed.