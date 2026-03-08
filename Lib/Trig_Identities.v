From Lib Require Import Imports Notations Trigonometry Reals_util Functions Sets.
Import FunctionNotations SetNotations.

Open Scope R_scope.

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

Lemma pythagorean_identity : forall (θ : ℝ),
  (sin θ)^2 + (cos θ)^2 = 1.
Proof.
  apply Trigonometry.pythagorean_identity.
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

Lemma sin_plus : forall x y : ℝ,
  sin (x + y) = sin x * cos y + cos x * sin y.
Proof.
  apply Trigonometry.sin_plus.
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

Lemma cos_plus : forall x y : ℝ,
  cos (x + y) = cos x * cos y - sin x * sin y.
Proof.
  apply Trigonometry.cos_plus.
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

Lemma tan_plus : forall x y : ℝ,
  cos (x + y) <> 0 -> cos x <> 0 -> cos y <> 0 -> 1 - tan x * tan y <> 0 ->
  tan (x + y) = (tan x + tan y) / (1 - tan x * tan y).
Proof.
  intros x y H1 H2 H3 H4. unfold tan. rewrite sin_plus, cos_plus.
  replace (sin x * cos y + cos x * sin y) with ((sin x / cos x + sin y / cos y) * (cos x * cos y)).
  - replace (cos x * cos y - sin x * sin y) with ((1 - (sin x / cos x) * (sin y / cos y)) * (cos x * cos y)).
    + field; repeat split; auto. rewrite <- cos_plus. exact H1.
    + field; split; assumption.
  - field; split; assumption.
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

Lemma sin_0 : sin 0 = 0.
Proof.
  apply Trigonometry.sin_0.
Qed.

Lemma cos_0_val : cos 0 = 1.
Proof.
  apply Trigonometry.cos_0.
Qed.

Lemma tan_0 : tan 0 = 0.
Proof.
  unfold tan. rewrite sin_0, cos_0_val. field.
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