From Calculus.Chapter1 Require Import Prelude.
From Calculus Require Import Problem_1_18.

Lemma lemma_1_19_a : forall x1 y1 x2 y2 α,
  x1 = α * y1 -> x2 = α * y2 -> α >= 0 ->
  x1 * y1 + x2 * y2 = √(x1^2 + x2^2) * √(y1^2 + y2^2).
Proof.
  intros x1 y1 x2 y2 α H1 H2 H3.
  assert (H4 : (x1 * y1 + x2 * y2)^2 = (√(x1^2 + x2^2) * √(y1^2 + y2^2))^2).
  { rewrite Rpow_mult_distr. repeat rewrite pow2_sqrt. 2 : { nra. } 2 : { nra. } rewrite H1. rewrite H2. nra. }
  apply Rsqr_inj. 2 : { rewrite <- sqrt_mult. 2 : { nra. } 2 : { nra. } apply sqrt_pos. } nra.
  repeat rewrite Rsqr_def. nra.
Qed.

Lemma lemma_1_19_a' : forall x1 y1 x2 y2,
  (y1 = 0 /\ y2 = 0) ->
  x1 * y1 + x2 * y2 = √(x1^2 + x2^2) * √(y1^2 + y2^2).
Proof.
  intros x1 y1 x2 y2 [H1 H2]. rewrite H1, H2.
  replace (x1 * 0 + x2 * 0) with 0 by nra. replace (0^2 + 0^2) with 0 by nra.
  rewrite sqrt_0. nra.
Qed.

Lemma lemma_1_19_a'' : forall x1 y1 x2 y2 α,
  (y1 <> 0 \/ y2 <> 0) -> α >= 0 -> ((x1 = α * y1 /\ x2 = α * y2) -> False) ->
  0 < (α * y1 - x1)^2 + (α * y2 - x2)^2.
Proof.
  intros x1 y1 x2 y2 α [H1 | H1] H2 H3.
  assert (x1 <> α * y1 \/ x2 <> α * y2) as [H4 | H4] by nra.
  - assert (H5 : (α * y2 - x2)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
    assert (H6 : 0 < (α * y1 - x1)^2). { rewrite <- Rsqr_pow2. apply Rsqr_pos_lt. nra. }
    nra.
  - assert (H5 : (α * y1 - x1)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
    assert (H6 : 0 < (α * y2 - x2)^2). { rewrite <- Rsqr_pow2. apply Rsqr_pos_lt. nra. }
    nra.
  - assert (x1 <> α * y1 \/ x2 <> α * y2) as [H4 | H4] by nra.
    -- assert (H5 : (α * y2 - x2)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
       assert (H6 : 0 < (α * y1 - x1)^2). { rewrite <- Rsqr_pow2. apply Rsqr_pos_lt. nra. }
       nra.
    -- assert (H5 : (α * y1 - x1)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
       assert (H6 : 0 < (α * y2 - x2)^2). { rewrite <- Rsqr_pow2. apply Rsqr_pos_lt. nra. }
       nra.
Qed.

Lemma lemma_1_19_a''' : forall x1 y1 x2 y2,
  y1 <> 0 \/ y2 <> 0 ->
  (forall α, (x1 <> α * y1 \/ x2 <> α * y2)) ->
  x1 * y1 + x2 * y2 < √(x1^2 + x2^2) * √(y1^2 + y2^2).
Proof.
  intros x1 y1 x2 y2 H1 H2.
  assert (H3 : forall α, α ^ 2 + -2 * (x1 * y1 + x2 * y2) / (y1 ^ 2 + y2 ^ 2) * α + (x1 ^ 2 + x2 ^ 2) / (y1 ^ 2 + y2 ^ 2) <> 0).
  {
    intros α. specialize (H2 α).
    assert (H3 : 0 < (α * y1 - x1)^2 + (α * y2 - x2)^2).
    {
     destruct H2 as [H2 | H2].
     - assert (H3 : (α * y2 - x2)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
       assert (H4 : 0 < (α * y1 - x1)^2). { rewrite <- Rsqr_pow2. apply Rsqr_pos_lt. nra. }
       nra.
     - assert (H3 : (α * y1 - x1)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
       assert (H4 : 0 < (α * y2 - x2)^2). { rewrite <- Rsqr_pow2. apply Rsqr_pos_lt. nra. }
       nra.
    }
    replace ((α * y1 - x1) ^ 2 + (α * y2 - x2) ^ 2) with
            (α^2 * (y1^2 + y2^2) + -2 * α * (x1 * y1 + x2 * y2) + x1^2 + x2^2) in H3 by nra.
    assert (H4 : α ^ 2 * (y1 ^ 2 + y2 ^ 2) + -2 * α * (x1 * y1 + x2 * y2) + x1 ^ 2 + x2 ^ 2 <> 0) by nra.
    assert (H5 : α^2 + ((-2 * (x1 * y1 + x2 * y2)) / (y1^2 + y2^2)) * α + (x1^2 + x2^2)/ (y1^2 + y2^2) > 0).
    { 
      apply Rmult_lt_compat_r with (r := 1 / (y1^2 + y2^2)) in H3. 2 : { apply Rdiv_pos_pos. nra. nra. } rewrite Rmult_0_l in H3.
      replace ((α ^ 2 * (y1 ^ 2 + y2 ^ 2) + -2 * α * (x1 * y1 + x2 * y2) + x1 ^ 2 + x2 ^ 2) * (1 / (y1 ^ 2 + y2 ^ 2))) with
              ((α ^ 2 * (y1 ^ 2 + y2 ^ 2) * (1 / (y1 ^ 2 + y2 ^ 2)) + -2 * α * (x1 * y1 + x2 * y2) * (1 / (y1 ^ 2 + y2 ^ 2)) + (x1 ^ 2 + x2 ^ 2) * (1 / (y1 ^ 2 + y2 ^ 2)))) in H3 by nra.
      replace ((α ^ 2 * (y1 ^ 2 + y2 ^ 2) * (1 / (y1 ^ 2 + y2 ^ 2)))) with (α^2) in H3 by (field; nra).
      replace ((-2 * α * (x1 * y1 + x2 * y2) * (1 / (y1 ^ 2 + y2 ^ 2)))) with
              ((-2 * (x1 * y1 + x2 * y2)) / (y1^2 + y2^2) * α) in H3 by nra. nra.
    }
    assert (H6 : α ^ 2 + -2 * (x1 * y1 + x2 * y2) / (y1 ^ 2 + y2 ^ 2) * α + (x1 ^ 2 + x2 ^ 2) / (y1 ^ 2 + y2 ^ 2) <> 0) by nra.
    nra.
  }
  apply lemma_1_18_a'' in H3.
  replace ((-2 * (x1 * y1 + x2 * y2) / (y1 ^ 2 + y2 ^ 2)) ^ 2) with
          ((4 * (x1 * y1 + x2 * y2) ^ 2) / ((y1 ^ 2 + y2 ^ 2) ^ 2)) in H3 by (field; nra).
  assert (H4 : (x1 * y1 + x2 * y2) ^ 2 / (y1 ^ 2 + y2 ^ 2) ^ 2 - ((x1 ^ 2 + x2 ^ 2) / (y1 ^ 2 + y2 ^ 2)) < 0) by nra.
  assert (H5 : (x1 * y1 + x2 * y2) ^ 2 / (y1 ^ 2 + y2 ^ 2) ^ 2  < (x1 ^ 2 + x2 ^ 2) / (y1 ^ 2 + y2 ^ 2)) by nra.
  assert (H6 : (y1^2 + y2^2 = 0) \/ (y1^2 + y2^2 <> 0)) by lra. destruct H6 as [H6 | H6].
  - nra.
  - assert (x1^2 + x2^2 = 0 \/ x1^2 + x2^2 <> 0) as [H20 | H20] by nra.
    {
      rewrite H20 in H5. rewrite Rdiv_0_l in H5. repeat rewrite <- Rsqr_pow2 in H5. rewrite <- Rsqr_div' in H5.
      assert (H21 : 0 <= ((x1 * y1 + x2 * y2) / (y1² + y2²))² ) by (apply Rle_0_sqr). nra.
    }
    apply Rmult_lt_compat_r with (r := (y1 ^ 2 + y2 ^ 2) ^ 2) in H5. 2 : { nra. }
    assert (0 < √(y1 ^ 2 + y2 ^ 2)) as H7. { apply sqrt_lt_R0. nra. }
    replace ((x1 * y1 + x2 * y2) ^ 2 / (y1 ^ 2 + y2 ^ 2) ^ 2 * (y1 ^ 2 + y2 ^ 2) ^ 2) with
            ((x1 * y1 + x2 * y2) ^ 2) in H5 by (field; nra).
    replace ((x1 ^ 2 + x2 ^ 2) / (y1 ^ 2 + y2 ^ 2) * (y1 ^ 2 + y2 ^ 2) ^ 2) with
            ((x1 ^ 2 + x2 ^ 2) * (y1 ^ 2 + y2 ^ 2)) in H5 by (field; nra).
    apply sqrt_lt_1 in H5. 2 : { rewrite <- Rsqr_pow2. apply Rle_0_sqr. } 2 : { nra. }
    pose proof Rtotal_order (x1 * y1 + x2 * y2) 0 as [H8 | [H8 | H8]].
    2 : {
        assert (H9 : (x1^2 + x2^2 = 0) \/ (x1^2 + x2^2 <> 0)) by lra. destruct H9 as [H9 | H9].
        - rewrite H9 in H5. rewrite H8 in H4. replace (0^2) with 0 in H5 by nra. rewrite Rmult_0_l in H5. rewrite sqrt_0 in H5.
          assert (H10 : 0 <= √((x1 * y1 + x2 * y2)^2)) by (apply sqrt_pos). nra.
        - rewrite H8. rewrite <- sqrt_mult. 2 : { nra. } 2 : { nra. } apply sqrt_lt_R0. nra.
    }
    2 : {
      assert (H9 : (x1^2 + x2^2 = 0) \/ (x1^2 + x2^2 <> 0)) by lra. destruct H9 as [H9 | H9].
      - rewrite H9 in H5. rewrite Rmult_0_l in H5. rewrite sqrt_0 in H5.
        assert (H10 : 0 <= √((x1 * y1 + x2 * y2)^2)) by (apply sqrt_pos). nra.
      - rewrite <- sqrt_mult. 2 : { nra. } 2 : { nra. } rewrite sqrt_pow2 in H5. 2 : { nra. } nra.
    }
    rewrite <- sqrt_mult. 2 : { nra. } 2 : { nra. }
    assert (H9 : 0 <= √((x1 ^ 2 + x2 ^ 2) * (y1 ^ 2 + y2 ^ 2))) by (apply sqrt_pos). nra.
Qed.

Lemma lemma_1_19_b : forall x y x1 y1 x2 y2,
  x = x1 / (√(x1^2 + x2^2)) -> y = y1 / (√(y1^2 + y2^2)) ->
  x = x2 / (√(x1^2 + x2^2)) -> y = y2 / (√(y1^2 + y2^2)) ->
  x1 * y1 + x2 * y2 <= √(x1^2 + x2^2) * √(y1^2 + y2^2).
Proof.
  intros x y x1 y1 x2 y2 H1 H2 H3 H4.
  assert (H5 : 0 <= x^2 - 2*x*y + y^2).
  { replace (x^2 - 2*x*y + y^2) with ((x - y)^2) by field. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
  assert (2*x*y <= x^2 + y^2) as H6 by nra. pose proof H6 as H7.
  rewrite H1 in H6. rewrite H2 in H6. rewrite H3 in H7. rewrite H4 in H7.
  replace ((x1 / √(x1 ^ 2 + x2 ^ 2)) ^ 2) with
          ((x1 ^ 2 / (√(x1 ^ 2 + x2 ^ 2)^2))) in H6.
          2 : { assert (x1^2 + x2^2 = 0 \/ x1^2 + x2^2 <> 0) as [H8 | H9] by lra.
                - rewrite H8. rewrite sqrt_0. simpl. repeat rewrite Rmult_0_l. unfold Rdiv. rewrite Rinv_0. nra.
                - field. assert (0 < √(x1 ^ 2 + x2 ^ 2)) as H10. { apply sqrt_lt_R0. nra. } nra.
              }
  rewrite pow2_sqrt in H6. 2 : { nra. }
  replace ((y1 / √(y1 ^ 2 + y2 ^ 2)) ^ 2) with
          ((y1 ^ 2 / (√(y1 ^ 2 + y2 ^ 2)^2))) in H6.
          2 : { assert (y1^2 + y2^2 = 0 \/ y1^2 + y2^2 <> 0) as [H8 | H9] by lra.
                - rewrite H8. rewrite sqrt_0. simpl. repeat rewrite Rmult_0_l. unfold Rdiv. rewrite Rinv_0. nra.
                - field. assert (0 < √(y1 ^ 2 + y2 ^ 2)) as H10. { apply sqrt_lt_R0. nra. } nra.
              }
  rewrite pow2_sqrt in H6. 2 : { nra. }
  replace ((x2 / √(x1 ^ 2 + x2 ^ 2)) ^ 2) with
          ((x2 ^ 2 / (√(x1 ^ 2 + x2 ^ 2)^2))) in H7.
          2 : { assert (x1^2 + x2^2 = 0 \/ x1^2 + x2^2 <> 0) as [H8 | H9] by lra.
                - rewrite H8. rewrite sqrt_0. simpl. repeat rewrite Rmult_0_l. unfold Rdiv. rewrite Rinv_0. nra.
                - field. assert (0 < √(x1 ^ 2 + x2 ^ 2)) as H10. { apply sqrt_lt_R0. nra. } nra.
              }
  rewrite pow2_sqrt in H7. 2 : { nra. }
  replace ((y2 / √(y1 ^ 2 + y2 ^ 2)) ^ 2) with
          ((y2 ^ 2 / (√(y1 ^ 2 + y2 ^ 2)^2))) in H7.
          2 : { assert (y1^2 + y2^2 = 0 \/ y1^2 + y2^2 <> 0) as [H8 | H9] by lra.
                - rewrite H8. rewrite sqrt_0. simpl. repeat rewrite Rmult_0_l. unfold Rdiv. rewrite Rinv_0. nra.
                - field. assert (0 < √(y1 ^ 2 + y2 ^ 2)) as H10. { apply sqrt_lt_R0. nra. } nra.
              }
  rewrite pow2_sqrt in H7. 2 : { nra. }
  replace (2 * (x1 / √(x1 ^ 2 + x2 ^ 2)) * (y1 / √(y1 ^ 2 + y2 ^ 2))) with
          ((2 * x1 * y1) / (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2))) in H6.
          2 :
          {
            assert ((√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2)) = 0 \/
                    (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2)) <> 0) as [H8 | H9] by lra.
            - rewrite H8. unfold Rdiv. rewrite Rinv_0. rewrite Rmult_0_r.
              assert (H9 : √(x1 ^ 2 + x2 ^ 2) = 0 \/ √(y1 ^ 2 + y2 ^ 2) = 0) by nra.
              destruct H9 as [H9 | H9].
              -- rewrite H9. rewrite Rinv_0. nra.
              -- rewrite H9. rewrite Rinv_0. nra.
            - field. nra.
          }
  replace (2 * (x2 / √(x1 ^ 2 + x2 ^ 2)) * (y2 / √(y1 ^ 2 + y2 ^ 2))) with
          ((2 * x2 * y2) / (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2))) in H7.
          2 :
          {
            assert ((√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2)) = 0 \/
                    (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2)) <> 0) as [H8 | H9] by lra.
            - rewrite H8. unfold Rdiv. rewrite Rinv_0. rewrite Rmult_0_r.
              assert (H9 : √(x1 ^ 2 + x2 ^ 2) = 0 \/ √(y1 ^ 2 + y2 ^ 2) = 0) by nra.
              destruct H9 as [H9 | H9].
              -- rewrite H9. rewrite Rinv_0. nra.
              -- rewrite H9. rewrite Rinv_0. nra.
            - field. nra.
          }
  assert (H8 :
    2 * x1 * y1 / (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2)) +
    2 * x2 * y2 / (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2)) <=
    x1 ^ 2 / (x1 ^ 2 + x2 ^ 2) + y1 ^ 2 / (y1 ^ 2 + y2 ^ 2) +
    x2 ^ 2 / (x1 ^ 2 + x2 ^ 2) + y2 ^ 2 / (y1 ^ 2 + y2 ^ 2)) by nra.
  replace (
    2 * x1 * y1 / (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2)) +
    2 * x2 * y2 / (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2)))
    with ((2 * x1 * y1 + 2 * x2 * y2) / (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2))) in H8 by nra.
  assert ((x1^2 + x2^2 = 0) \/ (x1^2 + x2^2 <> 0) /\ (y1^2 + y2^2 = 0) \/ (y1^2 + y2^2 <> 0)) as [H9 | H10] by lra.
  - assert (x1 = 0 /\ x2 = 0) as [H10 H11] by nra. rewrite H10, H11. replace (0^2 + 0^2) with 0 by nra. rewrite sqrt_0. nra.
  - destruct H10 as [[H10 H11] | H10].
    -- assert (y1 = 0 /\ y2 = 0) as [H12 H13] by nra. rewrite H12, H13. replace (0^2 + 0^2) with 0 by nra. rewrite sqrt_0. nra.
    -- assert (H11 : (x1^2 + x2^2 = 0) \/ (x1^2 + x2^2 <> 0)) by lra. destruct H11 as [H11 | H11].
       --- assert (x1 = 0 /\ x2 = 0) as [H12 H13] by nra. rewrite H12, H13. replace (0^2 + 0^2) with 0 by nra. rewrite sqrt_0. nra.
       --- replace (x1 ^ 2 / (x1 ^ 2 + x2 ^ 2) + y1 ^ 2 / (y1 ^ 2 + y2 ^ 2) + x2 ^ 2 / (x1 ^ 2 + x2 ^ 2) + y2 ^ 2 / (y1 ^ 2 + y2 ^ 2)) with
           2 in H8 by (field; nra).
           assert (H12 : √(x1 ^ 2 + x2 ^ 2) > 0). { apply sqrt_lt_R0. nra. }
           assert (H13 : √(y1 ^ 2 + y2 ^ 2) > 0). { apply sqrt_lt_R0. nra. }
           apply Rmult_le_compat_r with (r := (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2))) in H8. 2 : { nra. }
           replace ((2 * x1 * y1 + 2 * x2 * y2) / (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2)) *
                    (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2))) with
                   (2 * x1 * y1 + 2 * x2 * y2) in H8 by (field; nra). nra.
Qed.

Lemma lemma_1_19_c : forall x1 y1 x2 y2,
  x1 * y1 + x2 * y2 <= √(x1^2 + x2^2) * √(y1^2 + y2^2).
Proof.
  intros x1 y1 x2 y2.
  assert (H1 : (x1^2 + x2^2) * (y1^2 + y2^2) = (x1*y1 + x2*y2)^2 + (x1*y2 - x2*y1)^2) by nra.
  assert (H2 : (x1*y2 - x2*y1)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
  assert (H3 : (x1 * y1 + x2 * y2) ^ 2 <= (x1 ^ 2 + x2 ^ 2) * (y1 ^ 2 + y2 ^ 2)) by nra.
  assert (H4 : (x1 * y1 + x2 * y2)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
  apply sqrt_le_1 in H3. 2 : { nra. } 2 : { nra. }
  pose proof Rtotal_order (x1 * y1 + x2 * y2) 0 as [H5 | [H5 | H5]].
  2 : {
        rewrite H5. assert (H6 : 0 <= √(x1^2 + x2^2)). { apply sqrt_positivity. nra. }
        assert (H7 : 0 <= √(y1^2 + y2^2)). { apply sqrt_positivity. nra. } nra.
      }
  2 : { rewrite sqrt_pow2 in H3. 2 : { nra. } rewrite <- sqrt_mult. 2 : { nra. } 2 : { nra. } apply H3. }
  assert (H6 : √(x1^2 + x2^2) > 0). { apply sqrt_lt_R0. nra. }
  assert (H7 : √(y1^2 + y2^2) > 0). { apply sqrt_lt_R0. nra. }
  nra.
Qed.

Lemma contra_3 : forall P Q R,
  (P -> Q -> R) -> (~R -> ~P \/ ~Q).
Proof.
  intros P Q R H1. tauto.
Qed.

Lemma lemma_1_19_d_a : forall x1 y1 x2 y2,
  x1 * y1 + x2 * y2 = √(x1^2 + x2^2) * √(y1^2 + y2^2) ->
  ((y1 = 0 /\ y2 = 0) \/ exists α, x1 = α * y1 /\ x2 = α * y2).
Proof.
  intros x1 y1 x2 y2 H1.
  pose proof contra_3 (y1 <> 0 \/ y2 <> 0) (forall α, (x1 <> α * y1 \/ x2 <> α * y2))
                      (x1 * y1 + x2 * y2 < √(x1^2 + x2^2) * √(y1^2 + y2^2)) as H2.
  pose proof lemma_1_19_a''' x1 y1 x2 y2 as H3. apply H2 in H3.
  - destruct H3 as [H3 | H3].
    + left. nra.
    + right. apply not_all_ex_not in H3. destruct H3 as [α H3]. apply not_or_and in H3. destruct H3 as [H3 H4].
      exists α. nra.
  - apply Rle_not_lt. apply Req_le. apply sym_eq. apply H1.
Qed.

Lemma lemma_1_19_d_b : forall x y x1 y1 x2 y2,
  x = x1 / (√(x1^2 + x2^2)) -> y = y1 / (√(y1^2 + y2^2)) ->
  x = x2 / (√(x1^2 + x2^2)) -> y = y2 / (√(y1^2 + y2^2)) ->
  x1 * y1 + x2 * y2 = √(x1^2 + x2^2) * √(y1^2 + y2^2) ->
  ((y1 = 0 /\ y2 = 0) \/ exists α, x1 = α * y1 /\ x2 = α * y2).
Proof.
  intros x y x1 y1 x2 y2 H1 H2 H3 H4 H5.
  assert (H6 : x1^2 + x2^2 = 0 \/ x1^2 + x2^2 <> 0) by lra. destruct H6 as [H6 | H6].
  - assert (H7 : y1^2 + y2^2 = 0 \/ y1^2 + y2^2 <> 0) by lra. destruct H7 as [H7 | H7].
    + left. nra.
    + right. assert (H8 : x1 = 0 /\ x2 = 0) by nra. exists 0. nra.
  - assert (H7 : y1^2 + y2^2 = 0 \/ y1^2 + y2^2 <> 0) by nra. destruct H7 as [H7 | H7].
    + left. nra.
    + assert (H8 : 0 < √(x1^2 + x2^2)). { apply sqrt_lt_R0. nra. }
      assert (H9 : 0 < √(y1^2 + y2^2)). { apply sqrt_lt_R0. nra. }
      right. exists (√(x1^2 + x2^2) / √(y1^2 + y2^2)). split.
      * assert (H10 : x1 * y1 + x2 * y2 = 0 \/ x1 * y1 + x2 * y2 <> 0) by lra. destruct H10 as [H10 | H10].
        -- nra.
        -- apply Rmult_eq_compat_l with (r := 2 / (√(x1^2 + x2^2) * √(y1^2 + y2^2))) in H5.
           replace (2 / (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2)) * (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2))) with
                   2 in H5 by (field; nra). replace 2 with
                   (x1^2 / (x1^2 + x2^2) + y1^2 / (y1^2 + y2^2) + x2^2 / (x1^2 + x2^2) + y2^2 / (y1^2 + y2^2)) in H5 at 2 by (field; nra).
           replace (2 / (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2)) * (x1 * y1 + x2 * y2)) with
                   ((2*x1*y1 / (√(x1^2 + x2^2) * √(y1^2 + y2^2))) +
                    (2*x2*y2 / (√(x1^2 + x2^2) * √(y1^2 + y2^2)))) in H5 by (field; nra).
           replace (2 * x1 * y1 / (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2))) with (2 * x * y) in H5.
           2 : { rewrite H1. rewrite H2. field. nra. }
           replace (2 * x2 * y2 / (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2))) with (2 * x * y) in H5.
           2 : { rewrite H3. rewrite H4. field. nra. }
           assert (H11 : 4 * x * y = 2 * (x^2 + y^2)).
           {
              replace (2 * x * y + 2 * x * y) with (4 * x * y) in H5 by nra. simpl. repeat rewrite Rmult_1_r.
              replace (2 * (x * x + y * y)) with (x * x + y * y + x * x + y * y) by nra.
              rewrite H1 at 2 3. replace (x1 / √(x1 ^ 2 + x2 ^ 2) * (x1 / √(x1 ^ 2 + x2 ^ 2))) with
                      (x1^2 / (√(x1 ^ 2 + x2 ^ 2) * √(x1 ^ 2 + x2 ^ 2))) by (field; nra).
              rewrite sqrt_def. 2 : { nra. }
              rewrite H2 at 2 3. replace (y1 / √(y1 ^ 2 + y2 ^ 2) * (y1 / √(y1 ^ 2 + y2 ^ 2))) with
                      (y1^2 / (√(y1 ^ 2 + y2 ^ 2) * √(y1 ^ 2 + y2 ^ 2))) by (field; nra).
              rewrite sqrt_def. 2 : { nra. }
              rewrite H3 at 2 3. replace (x2 / √(x1 ^ 2 + x2 ^ 2) * (x2 / √(x1 ^ 2 + x2 ^ 2))) with
                      (x2^2 / (√(x1 ^ 2 + x2 ^ 2) * √(x1 ^ 2 + x2 ^ 2))) by (field; nra).
              rewrite sqrt_def. 2 : { nra. }
              rewrite H4 at 2 3. replace (y2 / √(y1 ^ 2 + y2 ^ 2) * (y2 / √(y1 ^ 2 + y2 ^ 2))) with
                      (y2^2 / (√(y1 ^ 2 + y2 ^ 2) * √(y1 ^ 2 + y2 ^ 2))) by (field; nra).
              rewrite sqrt_def. 2 : { nra. }
              nra.
           }
           assert (H12 : x = y) by nra.
           assert (x1 = 0 \/ x1 <> 0) as [H13 | H13] by nra.
           {
             rewrite H13 in H1. rewrite Rdiv_0_l in H1. rewrite H1 in H3.
             apply Rmult_eq_compat_r with (r := √(x1^2 + x2^2)) in H3.
             replace (x2 / √(x1 ^ 2 + x2 ^ 2) * √(x1 ^ 2 + x2 ^ 2)) with
                     (x2 * (√(x1 ^ 2 + x2 ^ 2) / √(x1 ^ 2 + x2 ^ 2))) in H3 by nra.
             rewrite Rdiv_diag in H3. nra. nra.
           }
           {
             replace x1 with (x * √(x1 ^ 2 + x2 ^ 2)) at 1. 2 : { rewrite H1. field. nra. }
             replace y1 with (y * √(y1 ^ 2 + y2 ^ 2)) at 2. 2 : { rewrite H2. field. nra. }
             replace (√(x1 ^ 2 + x2 ^ 2) / √(y1 ^ 2 + y2 ^ 2) * (y * √(y1 ^ 2 + y2 ^ 2))) with
                      (y * √(x1^2 + x2^2)) by (field; nra).
             apply Rmult_eq_reg_r with (r := / √(x1^2 + x2^2)). 2 : { apply Rinv_neq_0_compat. nra. }
             replace (x * √(x1 ^ 2 + x2 ^ 2) * / √(x1 ^ 2 + x2 ^ 2)) with x by (field; nra).
             replace (y * √(x1 ^ 2 + x2 ^ 2) * / √(x1 ^ 2 + x2 ^ 2)) with y by (field; nra).
             apply H12.
           }
      * assert (H10 : x1 * y1 + x2 * y2 = 0 \/ x1 * y1 + x2 * y2 <> 0) by lra. destruct H10 as [H10 | H10].
        -- nra.
        -- apply Rmult_eq_compat_l with (r := 2 / (√(x1^2 + x2^2) * √(y1^2 + y2^2))) in H5.
           replace (2 / (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2)) * (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2))) with
                   2 in H5 by (field; nra).
           replace 2 with (x1^2 / (x1^2 + x2^2) + y1^2 / (y1^2 + y2^2) + x2^2 / (x1^2 + x2^2) + y2^2 / (y1^2 + y2^2)) in H5 at 2 by (field; nra).
           replace (2 / (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2)) * (x1 * y1 + x2 * y2)) with
                   ((2*x1*y1 / (√(x1^2 + x2^2) * √(y1^2 + y2^2))) +
                    (2*x2*y2 / (√(x1^2 + x2^2) * √(y1^2 + y2^2)))) in H5 by (field; nra).
           replace (2 * x1 * y1 / (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2))) with (2 * x * y) in H5.
           2 : { rewrite H1. rewrite H2. field. nra. }
           replace (2 * x2 * y2 / (√(x1 ^ 2 + x2 ^ 2) * √(y1 ^ 2 + y2 ^ 2))) with (2 * x * y) in H5.
           2 : { rewrite H3. rewrite H4. field. nra. }
           assert (H11 : 4 * x * y = 2 * (x^2 + y^2)).
           {
              replace (2 * x * y + 2 * x * y) with (4 * x * y) in H5 by nra. simpl. repeat rewrite Rmult_1_r.
              replace (2 * (x * x + y * y)) with (x * x + y * y + x * x + y * y) by nra.
              rewrite H1 at 2 3. replace (x1 / √(x1 ^ 2 + x2 ^ 2) * (x1 / √(x1 ^ 2 + x2 ^ 2))) with
                      (x1^2 / (√(x1 ^ 2 + x2 ^ 2) * √(x1 ^ 2 + x2 ^ 2))) by (field; nra).
              rewrite sqrt_def. 2 : { nra. }
              rewrite H2 at 2 3. replace (y1 / √(y1 ^ 2 + y2 ^ 2) * (y1 / √(y1 ^ 2 + y2 ^ 2))) with
                      (y1^2 / (√(y1 ^ 2 + y2 ^ 2) * √(y1 ^ 2 + y2 ^ 2))) by (field; nra).
              rewrite sqrt_def. 2 : { nra. }
              rewrite H3 at 2 3. replace (x2 / √(x1 ^ 2 + x2 ^ 2) * (x2 / √(x1 ^ 2 + x2 ^ 2))) with
                      (x2^2 / (√(x1 ^ 2 + x2 ^ 2) * √(x1 ^ 2 + x2 ^ 2))) by (field; nra).
              rewrite sqrt_def. 2 : { nra. }
              rewrite H4 at 2 3. replace (y2 / √(y1 ^ 2 + y2 ^ 2) * (y2 / √(y1 ^ 2 + y2 ^ 2))) with
                      (y2^2 / (√(y1 ^ 2 + y2 ^ 2) * √(y1 ^ 2 + y2 ^ 2))) by (field; nra).
              rewrite sqrt_def. 2 : { nra. }
              nra.
           }
           assert (H12 : x = y) by nra.
           assert (x2 = 0 \/ x2 <> 0) as [H13 | H13] by nra.
           {
             rewrite H13 in H3. rewrite Rdiv_0_l in H3. rewrite H3 in H1.
             apply Rmult_eq_compat_r with (r := √(x1^2 + x2^2)) in H1.
             replace (x1 / √(x1 ^ 2 + x2 ^ 2) * √(x1 ^ 2 + x2 ^ 2)) with
                     (x1 * (√(x1 ^ 2 + x2 ^ 2) / √(x1 ^ 2 + x2 ^ 2))) in H1 by nra.
             rewrite Rdiv_diag in H1. nra. nra.
           }
           {
             replace x2 with (x * √(x1 ^ 2 + x2 ^ 2)) at 1. 2 : { rewrite H3. field. nra. }
             replace y2 with (y * √(y1 ^ 2 + y2 ^ 2)) at 2. 2 : { rewrite H4. field. nra. }
             replace (√(x1 ^ 2 + x2 ^ 2) / √(y1 ^ 2 + y2 ^ 2) * (y * √(y1 ^ 2 + y2 ^ 2))) with
                      (y * √(x1^2 + x2^2)) by (field; nra).
             apply Rmult_eq_reg_r with (r := / √(x1^2 + x2^2)). 2 : { apply Rinv_neq_0_compat. nra. }
             replace (x * √(x1 ^ 2 + x2 ^ 2) * / √(x1 ^ 2 + x2 ^ 2)) with x by (field; nra).
             replace (y * √(x1 ^ 2 + x2 ^ 2) * / √(x1 ^ 2 + x2 ^ 2)) with y by (field; nra).
             apply H12.
           }
Qed.

Lemma lemma_1_19_d_c : forall x1 y1 x2 y2,
  x1 * y1 + x2 * y2 = √(x1^2 + x2^2) * √(y1^2 + y2^2) ->
  ((y1 = 0 /\ y2 = 0) \/ exists α, x1 = α * y1 /\ x2 = α * y2).
Proof.
  intros x1 y1 x2 y2 H1.
  assert (H2 : (x1^2 + x2^2) * (y1^2 + y2^2) = (x1*y1 + x2*y2)^2 + (x1*y2 - x2*y1)^2) by nra.
  assert (H3 : x1 * y2 - x2 * y1 = 0 \/ x1 * y2 - x2 * y1 <> 0) by lra. destruct H3 as [H3 | H3].
  - rewrite H3 in H2. replace (0^2) with 0 in H2 by nra. rewrite Rplus_0_r in H2.
    assert (H4 : x1 * y2 = x2 * y1) by nra.
    assert (H5 : (y1 = 0 /\ y2 = 0) \/ (y1 = 0 /\ y2 <> 0) \/ (y1 <> 0 /\ y2 = 0) \/ (y1 <> 0 /\ y2 <> 0)) by lra.
    destruct H5 as [[H5 H6] | [[H5 H6] | [[H5 H6] | [H5 H6]]]].
    -- left. nra.
    -- right. exists (x2 / y2). split.
       --- replace (x2 / y2 * y1) with ((x2 * y1) / y2) by (field; nra). rewrite <- H4. field. nra.
       --- replace (x2 / y2 * y2) with ((x2 * y2) / y2) by (field; nra). field. nra.
    -- right. assert (H7 : x2 = 0) by nra. exists (x1 / y1). split.
       --- replace (x1 / y1 * y1) with ((x1 * y1) / y1) by (field; nra). field. nra.
       --- rewrite H7. rewrite H6. nra.
    -- right. exists (x1 / y1). split.
       --- replace (x1 / y1 * y1) with ((x1 * y1) / y1) by (field; nra). field. nra.
       --- replace (x1 / y1 * y2) with ((x1 * y2) / y1) by (field; nra). rewrite H4. field. nra.
  - assert (H4 : x1 <> 0 \/ x2 <> 0) by nra. assert (H5 : y1 <> 0 \/ y2 <> 0) by nra.
    assert (H6 : x1^2 + x2^2 > 0) by nra. assert (H7 : y1^2 + y2^2 > 0) by nra.
    rewrite <- sqrt_mult in H1. 2 : { nra. } 2 : { nra. }
    assert (H8 : √(x1 ^ 2 + x2 ^ 2) > 0). { apply sqrt_lt_R0. nra. }
    assert (H9 : (x1*y1 + x2*y2)^2 = √(x1^2 + x2^2)^2 * √(y1^2 + y2^2)^2).
    { rewrite H1. rewrite pow2_sqrt. 2 : { nra. } rewrite pow2_sqrt. 2 : { nra. } rewrite pow2_sqrt. 2 : { nra. } reflexivity. }
    rewrite pow2_sqrt in H9. 2 : { nra. } rewrite pow2_sqrt in H9. 2 : { nra. } nra.
Qed.