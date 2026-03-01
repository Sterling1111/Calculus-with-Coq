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

Lemma derivative_at_sin : forall x, ⟦ der x ⟧ sin = cos.
Proof.
  
Admitted.

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
  apply derivative_on_pos_imp_increasing_on with (f' := cos); try lra.
  - pose proof π_pos as H1. lra.
  - apply derivative_imp_derivative_on.
    + apply differentiable_domain_closed; pose proof π_pos as H1. lra.
    + apply derivative_sin.
  - intros x H1. admit.
Admitted.

Lemma cos_decreasing_on : decreasing_on cos [0, π].
Proof.
  apply derivative_on_neg_imp_decreasing_on with (f' := (- sin)%function); try lra.
  - pose proof π_pos as H1. lra.
  - apply derivative_imp_derivative_on.
    + apply differentiable_domain_closed; pose proof π_pos as H1. lra.
    + apply derivative_cos.
  - intros x H1. admit.
Admitted.

Lemma tan_increasing_on : increasing_on tan (-(π/2), π/2).
Proof.

Admitted.

Lemma sin_bounds : forall x,
  -1 <= sin x <= 1.
Proof.
  admit.
Admitted.

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
  admit.
Admitted.

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

Lemma tan_bijective : bijective_on tan (-(π / 2), π / 2) R.
Proof.
  split; [| split].
  - intros x H1. apply Full_intro.
  - apply increasing_on_imp_one_to_one_on. apply tan_increasing_on.
  - intros y H1. admit.
Admitted.

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

Lemma exists_tan_inverse : exists f, inverse_on tan f (-(π / 2), π / 2) R.
Proof.
  pose proof tan_bijective as H1.
  pose proof exists_inverse_on_iff tan (-(π / 2), π / 2) R as H2.
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

Definition arctan_sig : {f : R -> R | inverse_on tan f (-(π / 2), π / 2) R}.
Proof.
  apply constructive_indefinite_description, exists_tan_inverse.
Qed.

Definition arcsin (y : R) : R := proj1_sig arcsin_sig y.

Definition arccos (y : R) : R := proj1_sig arccos_sig y.

Definition arctan (y : R) : R := proj1_sig arctan_sig y.

Lemma arcsin_spec : inverse_on sin arcsin [-(π/2), π/2] [-1, 1].
Proof.
  unfold arcsin. destruct arcsin_sig as [f_inv H1]. auto.
Qed.

Lemma arccos_spec : inverse_on cos arccos [0, π] [-1, 1].
Proof.
  unfold arccos. destruct arccos_sig as [f_inv H1]. auto.
Qed.

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
  rewrite <- (H4 (arctan x + arctan y)); [ f_equal | ].
  rewrite tan_plus.
  - rewrite !H5; try apply Full_intro. reflexivity.
  - admit.
  - admit.
  - admit.
  - admit. 
Admitted.

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
Proof. admit. Admitted.

Lemma tan_0 : tan 0 = 0.
Proof. 
  unfold tan. rewrite sin_0, cos_0. lra. 
Qed.

Lemma left_limit_cos : forall a,
  ⟦ lim a⁻ ⟧ cos = cos a.
Proof. admit.
Admitted.

Lemma right_limit_cos : forall a,
  ⟦ lim a⁺ ⟧ cos = cos a.
Proof. admit.
Admitted.

Lemma limit_cos : forall a,
  ⟦ lim a ⟧ cos = cos a.
Proof.
  intros a.
  apply limit_iff; split; [ apply left_limit_cos | apply right_limit_cos ].
Qed.

Lemma left_limit_sin : forall a,
  ⟦ lim a⁻ ⟧ sin = sin a.
Proof. admit.
Admitted. 

Lemma right_limit_sin : forall a,
  ⟦ lim a⁺ ⟧ sin = sin a.
Proof. admit.
Admitted.

Lemma limit_sin : forall a,
  ⟦ lim a ⟧ sin = sin a.
Proof.
  intros a.
  apply limit_iff; split; [ apply left_limit_sin | apply right_limit_sin ].
Qed.

Lemma continuous_on_tan : continuous_on tan (-π / 2, π / 2).
Proof.
  apply differentiable_on_imp_continuous_on_open.
  - pose proof π_pos; lra.
  - apply derivative_on_imp_differentiable_on with (f' := (sec ^ 2)%function); try lra.
    intros x H1. left. split. auto_interval. apply derivative_at_tan.
    admit.
Admitted.

Lemma inf_differentiable_cos : inf_differentiable cos.
Proof.
  assert (H_closed : forall f, 
    f = cos \/ f = sin \/ f = (fun x => -cos x) \/ f = (fun x => -sin x) ->
    exists f', derivative f f' /\ (f' = cos \/ f' = sin \/ f' = (fun x => -cos x) \/ f' = (fun x => -sin x))).
  {
    intros f [H | [H | [H | H]]]; subst.
    - exists (- sin)%function. split; [apply derivative_cos | right; right; right; reflexivity].
    - exists cos. split; [apply derivative_sin | left; reflexivity].
    - exists sin. split. 
      + replace sin with (fun x => - (- sin x)) by (extensionality x; lra). 
        apply derivative_neg. apply derivative_cos.
      + right; left; reflexivity.
    - exists (- cos)%function. split; [apply derivative_neg; apply derivative_sin | right; right; left; reflexivity].
  }
  assert (H_inv : forall n, exists fn, nth_derivative n cos fn /\ (fn = cos \/ fn = sin \/ fn = (fun x => -cos x) \/ fn = (fun x => -sin x))).
  {
    induction n.
    - exists cos. split; [simpl; reflexivity | left; reflexivity].
    - destruct IHn as [fk [H1 H2]].
      apply H_closed in H2 as [fk' [H3 H4]].
      exists fk'. split; auto.
      simpl. exists fk. split; auto.
  }
  intro n. destruct (H_inv n) as [fn [H1 H2]]. exists fn. apply H1.
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
Proof. admit. Admitted.

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
Admitted.

Lemma derivative_at_arccos : forall x, -1 < x < 1 -> ⟦ der x ⟧ arccos = (fun x => - 1 / sqrt (1 - x ^ 2)).
Proof.
  intros x H1.
Admitted.

Lemma derivative_arctan : ⟦ der ⟧ arctan = (fun x => 1 / (1 + x ^ 2)).
Proof.
Admitted.

Lemma arctan_0 : arctan 0 = 0.
Proof.
  pose proof arctan_spec as [H1 [H2 [H3 H4]]].
  rewrite <- H3; auto. rewrite tan_0; auto.
  pose proof π_pos as H5. solve_R.
Qed.