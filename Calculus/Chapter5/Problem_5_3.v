From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_3_i : ⟦ lim 0 ⟧ (λ x, x * (3 - cos (x^2))) = 0.
Proof.
  unfold limit. intros ε H1. exists (ε / 4).
  split; [lra |].
  intros x H2. pose proof (cos_bounds (x^2)) as H3.
  replace (x * (3 - cos (x^2)) - 0) with (x * (3 - cos (x^2))) by lra.
  rewrite Rminus_0_r in H2. rewrite Rabs_mult.
  assert (H4 : |3 - cos (x^2)| = 3 - cos (x^2)) by (apply Rabs_pos_eq; lra).
  rewrite H4; nra.
Qed.

Lemma lemma_5_3_ii : ⟦ lim 2 ⟧ (λ x, x^2 + 5 * x - 2) = 12.
Proof.
  intros ε H1. exists (Rmin 1 (ε / 10)). split; solve_R.
Qed.

Lemma lemma_5_3_iii : ⟦ lim 1 ⟧ (λ x, 100 / x) = 100.
Proof.
  intros ε H1. exists (Rmin (1 / 2) (ε / 200)). split; [solve_R |].
  intros x [H2 H3].
  assert (H4 : |x - 1| < 1 / 2) by solve_R.
  assert (H5 : |x - 1| < ε / 200) by solve_R.
  assert (H6 : |x| > 1 / 2) by solve_R.
  replace (100 / x - 100) with (100 * ((1 - x) / x)) by (field; solve_R).
  rewrite Rabs_mult, Rabs_right, Rabs_div, Rabs_minus_sym; try lra.
  apply Rlt_trans with (100 * (|x - 1| / (1 / 2))); [ | lra ].
  apply Rmult_lt_compat_l; try lra.
  apply cross_multiply_lt; solve_R.
Qed.

Lemma lemma_5_3_iv (a : R) : ⟦ lim a ⟧ (λ x, x^4) = a^4.
Proof.
  unfold limit. intros ε H1.
  exists (Rmin 1 (ε / (4 * (|a| + 1)^3 + 1))).
  split.
  - unfold Rmin. destruct (Rle_dec 1 (ε / (4 * (|a| + 1) ^ 3 + 1))) as [H2 | H2]; [lra | ].
    pose proof (Rabs_pos a) as H3.
    apply Rdiv_lt_0_compat; [apply H1 | ].
    assert (H4 : 0 < |a| + 1) by lra.
    pose proof (pow_lt (|a| + 1) 3 H4) as H5.
    lra.
  - intros x H2. destruct H2 as [H3 H4].
    assert (H5 : |x - a| < 1) by (eapply Rlt_le_trans; [apply H4 | apply Rmin_l]).
    assert (H6 : |x - a| < ε / (4 * (|a| + 1)^3 + 1)) by (eapply Rlt_le_trans; [apply H4 | apply Rmin_r]).
    replace (x^4 - a^4) with ((x - a) * (x^3 + x^2 * a + x * a^2 + a^3)) by lra.
    rewrite Rabs_mult.
    assert (H7 : |x| < |a| + 1).
    { replace x with ((x - a) + a) by lra.
      pose proof (Rabs_triang (x - a) a) as H8; lra. }
    assert (H8 : |x^3 + x^2 * a + x * a^2 + a^3| < 4 * (|a| + 1)^3 + 1).
    { apply Rabs_def1;
      assert (H9 : - (|a| + 1) < x < |a| + 1) by (apply Rabs_def2 in H7; lra);
      assert (H10 : - |a| <= a <= |a|) by solve_R;
      pose proof (Rabs_pos a) as H11;
      replace (x^3 + x^2 * a + x * a^2 + a^3) with ((x^2 + a^2) * (x + a)) by lra;
      assert (H12 : 0 <= x^2 + a^2) by nra;
      assert (H13 : x^2 + a^2 < 2 * (|a| + 1)^2) by nra;
      assert (H14 : - (2 * |a| + 1) < x + a < 2 * |a| + 1) by nra;
      nra. }
    pose proof (Rabs_pos (x - a)) as H9.
    pose proof (Rabs_pos (x^3 + x^2 * a + x * a^2 + a^3)) as H10.
    assert (H11 : 0 < 4 * (|a| + 1) ^ 3 + 1).
    { pose proof (Rabs_pos a) as H12.
      assert (H13 : 0 < |a| + 1) by lra.
      pose proof (pow_lt (|a| + 1) 3 H13) as H14; lra. }
    assert (H12 : |x - a| * (4 * (|a| + 1) ^ 3 + 1) < ε).
    { apply (Rmult_lt_compat_r (4 * (|a| + 1) ^ 3 + 1)) in H6; auto.
      unfold Rdiv in H6. rewrite Rmult_assoc in H6.
      assert (H13 : / (4 * (|a| + 1) ^ 3 + 1) * (4 * (|a| + 1) ^ 3 + 1) = 1) by (apply Rinv_l; lra).
      rewrite H13 in H6; lra. }
    nra.
Qed.

Lemma lemma_5_3_v : ⟦ lim 1 ⟧ (λ x, x^4 + 1 / x) = 2.
Proof.
Admitted.

Lemma lemma_5_3_vi : ⟦ lim 0 ⟧ (λ x, x / (2 - (sin x)^2)) = 0.
Proof.
Admitted.

Lemma lemma_5_3_vii : ⟦ lim 0 ⟧ (λ x, √(|x|)) = 0.
Proof.
Admitted.

Lemma lemma_5_3_viii : ⟦ lim 1 ⟧ (λ x, √x) = 1.
Proof.
Admitted.