From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_3_i : ⟦ lim 0 ⟧ (λ x, x * (3 - cos (x^2))) = 0.
Proof.
  intros ε H1. exists (Rmin 1 (ε / 4)). split; [ solve_R | ].
  intros x H2. pose proof (cos_bounds (x^2)) as H3.
  rewrite Rminus_0_r, Rabs_mult in *.
  apply Rle_lt_trans with (r2 := |x| * 4); [ | solve_R ].
  apply Rmult_le_compat_l; [ solve_R | apply Rabs_le; lra ].
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
  intros ε H1. exists (Rmin 1 (ε / (5 * (|a| + 1) ^ 3))).
  split.
  { apply Rmin_case; [ lra | ]. apply Rdiv_pos_pos; solve_R. }
  intros x [H2 H3].
Admitted.

Lemma lemma_5_3_v : ⟦ lim 1 ⟧ (λ x, x^4 + 1 / x) = 2.
Proof.
Admitted.

Lemma lemma_5_3_vi : ⟦ lim 0 ⟧ (λ x, x / (2 - (sin x)^2)) = 0.
Admitted.

Lemma lemma_5_3_vii : ⟦ lim 0 ⟧ (λ x, sqrt (|x|)) = 0.
Proof.
Admitted.

Lemma lemma_5_3_viii : ⟦ lim 1 ⟧ (λ x, sqrt x) = 1.
Proof.
Admitted.