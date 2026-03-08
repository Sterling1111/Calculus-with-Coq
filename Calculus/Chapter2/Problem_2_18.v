From Calculus.Chapter2 Require Import Prelude.

Lemma lemma_2_18_a : forall (x : R) (l : list Z),
  (sum_f 0 (length l) (fun i => IZR (nth i l 1%Z) * x ^ i) = 0) -> (irrational x \/ is_integer x).
Proof.
  intros x l H1. assert (rational x \/ irrational x) as [H2 | H2] by apply classic; auto; right.
  destruct H2 as [p [q H2]]. assert ((p = 0 \/ q = 0) \/ (p <> 0 /\ q <> 0))%Z as [[H3 | H3] | [H3 H4]] by lia.
  - assert (x = 0) as H4. { rewrite H2. rewrite H3. lra. } rewrite H4. exists 0%Z. reflexivity.
  - assert (x = 0) as H4. { rewrite H2. rewrite H3. unfold Rdiv. rewrite Rinv_0. lra. } rewrite H4. exists 0%Z. reflexivity.
  - pose proof (rational_representation x p q H3 H4 H2) as [p' [q' [H6 H7]]]. assert (H8 : x <> 0). { rewrite H2. apply div_nonzero. apply not_0_IZR. apply H3. apply not_0_IZR. apply H4. }
    assert (H9 : (p' <> 0)%Z). { apply x_neq_0_IZR_num_neq_0 with (x := x) (z := q'); tauto. } assert (H10 : (q' <> 0)%Z). { apply x_neq_0_IZR_den_neq_0 with (x := x) (y := p'); tauto. }
    rewrite H6 in H1. apply Rmult_eq_compat_l with (r := IZR q' ^ (length l)) in H1.
    rewrite Rmult_0_r in H1. rewrite r_mult_sum_f_i_n_f in H1. replace (sum_f 0 (length l) (fun i : nat => IZR (nth i l 1%Z) * (IZR p' / IZR q') ^ i * IZR q' ^ length l)) with 
    (sum_f 0 (length l) (fun i : nat => IZR (nth i l 1%Z) * IZR p' ^ i * IZR q' ^ (length l - i))) in H1.
     2 : { apply sum_f_equiv; try lia. intros i H11. rewrite Rmult_assoc with (r2 := (IZR p' / IZR q') ^ i). rewrite Rpow_div_l; try (apply not_0_IZR; tauto). field_simplify.
           2 : { rewrite pow_IZR. apply not_0_IZR. apply Z.pow_nonzero; lia. }
          rewrite pow_sub; try lia. lra. apply not_0_IZR; auto.
         }
    assert (q' = 1 \/ q' = -1 \/ (q' <> 1 /\ q' <> -1))%Z as [H11 | [H11 | H11]] by lia.
    -- exists p'. rewrite H6. rewrite H11. lra.
    -- exists (-p')%Z. rewrite H6. rewrite H11. replace (-p')%Z with (-1 * p')%Z by lia. rewrite mult_IZR. nra.
    -- pose proof (prime_divides_2 (q')) as [a [H12 [b H13]]]; try lia.
       replace ((fun i : nat => IZR (nth i l 1%Z) * IZR p' ^ i * IZR q' ^ (length l - i))) with ((fun i : nat => IZR ((nth i l 1%Z) * p' ^ Z.of_nat i * q' ^ Z.of_nat(length l - i)))) in H1.
       2 : { apply functional_extensionality. intros i. repeat rewrite pow_IZR. repeat rewrite <- mult_IZR. reflexivity. }
       destruct l as [| h t]. { rewrite sum_f_0_0 in H1. simpl in H1; lra. } replace (length (h :: t)) with (S (length t)) in H1 by reflexivity.
       rewrite sum_f_i_Sn_f in H1; try lia. assert (H14 : (IZR a | sum_f 0 (length t) (fun i : nat => IZR (nth i (h :: t) 1%Z * p' ^ Z.of_nat i * q' ^ Z.of_nat (S (length t) - i))))).
       { 
          apply R_divides_sum; try lia. intros j H14. apply IZR_divides. exists (nth j (h :: t) 1 * p' ^ Z.of_nat j * q' ^ Z.of_nat (length t - j) * b)%Z.
          assert (nth j (h :: t) 1 * p' ^ Z.of_nat j = 0 \/ nth j (h :: t) 1 * p' ^ Z.of_nat j <> 0)%Z as [H15 | H15] by lia.
          - rewrite H15. lia.
          - pose proof Z.mul_cancel_l (q' ^ Z.of_nat (S (length t) - j))%Z (q' ^ Z.of_nat (length t - j) * b * a)%Z (nth j (h :: t) 1 * p' ^ Z.of_nat j)%Z as [_ H16]; auto.
            replace ((nth j (h :: t) 1 * p' ^ Z.of_nat j * q' ^ Z.of_nat (length t - j) * b * a)%Z) with ((nth j (h :: t) 1 * p' ^ Z.of_nat j * (q' ^ Z.of_nat (length t - j) * b * a))%Z) by lia. apply H16. clear H15 H16.
            replace (S (length t) - j)%nat with (S (length t - j))%nat by lia. replace (Z.of_nat (S (length t - j))) with (Z.succ (Z.of_nat (length t - j))) by lia. rewrite Z.pow_succ_r; lia.
       }
       assert (H15 : (IZR a | IZR (nth (S (length t)) (h :: t) 1%Z * p' ^ Z.of_nat (S (length t)) * q' ^ Z.of_nat (S (length t) - S (length t))))).
       {
          replace (IZR (nth (S (length t)) (h :: t) 1%Z * p' ^ Z.of_nat (S (length t)) * q' ^ Z.of_nat (S (length t) - S (length t)))) with 
          (- sum_f 0 (length t) (fun i : nat => IZR (nth i (h :: t) 1%Z * p' ^ Z.of_nat i * q' ^ Z.of_nat (S (length t) - i)))) by lra.
          apply divides_neg_R. apply H14.
       }
       apply IZR_divides in H15. replace (nth (S (length t)) (h :: t) 1)%Z with 1%Z in H15. 2 : { simpl. rewrite nth_overflow; lia. } rewrite Z.mul_1_l in H15.
       replace (q' ^ Z.of_nat (S (length t) - S (length t)))%Z with 1%Z in H15. 2 : { replace (S (length t) - S (length t))%nat with 0%nat by lia. lia. }
       rewrite Z.mul_1_r in H15.  apply prime_div_pow_div_Z in H15. 2 : { apply Znt.prime_alt; auto. } assert (H16 : (a | q')%Z). { exists b. lia. }
       assert (H17 : (a > 1)%Z) by (destruct H12; lia). specialize (H7 a H17); tauto.
Qed.

Lemma sqrt_2_lt_sqrt_3 : sqrt 2 < sqrt 3.
Proof.
  apply Rsqr_incrst_0; try (apply sqrt_positivity; lra). unfold Rsqr. repeat rewrite sqrt_sqrt; lra.
Qed.

Lemma sqrt_6_lt_sqrt_2_plus_sqrt_3 : sqrt 6 < sqrt 2 + sqrt 3.
Proof.
  assert (0 <= sqrt 6 /\ 0 <= sqrt 2 /\ 0 <= sqrt 3) as [H1 [H2 H3]] by (repeat split; apply sqrt_positivity; lra).
  apply Rsqr_incrst_0; try lra.
  unfold Rsqr. rewrite sqrt_sqrt; try lra. field_simplify.
  repeat rewrite pow2_sqrt; try lra. rewrite Rmult_assoc. rewrite <- sqrt_mult; try lra. replace (2 * 3) with 6 by lra.
  apply Rsqr_incrst_0; try lra. unfold Rsqr. field_simplify. repeat rewrite pow2_sqrt; try lra.
Qed.

Lemma sqrt_2_plus_sqrt_3_lt_1_plus_sqrt_6 : sqrt 2 + sqrt 3 < 1 + sqrt 6.
Proof.
  assert (0 <= sqrt 6 /\ 0 <= sqrt 2 /\ 0 <= sqrt 3) as [H1 [H2 H3]] by (repeat split; apply sqrt_positivity; lra).
  apply Rsqr_incrst_0; try lra.
  unfold Rsqr. field_simplify. repeat rewrite pow2_sqrt; try lra. field_simplify.
  replace (2 * sqrt 2 * sqrt 3) with (2 * sqrt 6) by (rewrite Rmult_assoc; rewrite <- sqrt_mult; try lra; replace (2 * 3) with 6 by lra; lra).
  apply Rplus_lt_compat_l; lra.
Qed.

Lemma sqrt_2_plus_sqrt_3_minus_sqrt_6_gt_0 : sqrt 2 + sqrt 3 - sqrt 6 > 0.
Proof.
  pose proof sqrt_6_lt_sqrt_2_plus_sqrt_3 as H1. lra.
Qed.

Lemma sqrt_2_plus_sqrt_3_minus_sqrt_6_lt_1 : sqrt 2 + sqrt 3 - sqrt 6 < 1.
Proof.
  pose proof sqrt_2_plus_sqrt_3_lt_1_plus_sqrt_6 as H1. lra.
Qed.

Lemma lemma_2_18_b : irrational (sqrt 6 - sqrt 2 - sqrt 3).
Proof.
  set (x := sqrt 6 - sqrt 2 - sqrt 3). assert (x^2 = 11 + 2 * sqrt 6 * (1 - (sqrt 2 + sqrt 3))) as H1.
  { 
    unfold x. field_simplify. repeat rewrite pow2_sqrt; try lra. field_simplify.
    replace ( 2 * sqrt 2 * sqrt 3) with (2 * sqrt 6).
    2 : { rewrite Rmult_assoc. rewrite <- sqrt_mult; try lra. replace (2 * 3) with 6 by lra. lra. } lra. 
  }
  assert (H2 : (x^2 - 11)^2 = 144 + 48 * x).
  {
    replace ((x^2 - 11)^2) with (24 * (1 - (sqrt 2 + sqrt 3))^2). 2 : { rewrite H1. field_simplify. repeat rewrite pow2_sqrt; try lra. }
    replace ((1 - (sqrt 2 + sqrt 3)) ^ 2) with ((1 + (sqrt 2 + sqrt 3)^2 - 2 * (sqrt 2 + sqrt 3))) by lra.
    replace ((1 + (sqrt 2 + sqrt 3) ^ 2 - 2 * (sqrt 2 + sqrt 3))) with (6 + 2 * (sqrt 6 - sqrt 2 - sqrt 3)).
    2 : { field_simplify. repeat rewrite pow2_sqrt; try lra. field_simplify. replace (2 * sqrt 2 * sqrt 3) with (2 * sqrt 6).
      2 : { rewrite Rmult_assoc. rewrite <- sqrt_mult; try nra. replace (2 * 3) with 6 by lra. lra. } lra. }
    fold x. lra.
  }
  assert (H3 : (x^2 - 11)^2 = x^4 - 22 * x^2 + 121) by nra.
  assert (H4 : x^4 - 22 * x^2 - 48 * x - 23 = 0) by nra.
  assert (H5 : sum_f 0 4 (fun i => IZR (nth i [-23; -48; -22; 0]%Z 1%Z) * x ^ i) = 0).
  { repeat rewrite sum_f_i_Sn_f; try rewrite sum_f_0_0; try lia. simpl. field_simplify. nra. }
  apply lemma_2_18_a in H5 as [H5 | H5]; auto. assert (H6 : sqrt 6 - sqrt 2 - sqrt 3 > -1).
  { pose proof sqrt_2_plus_sqrt_3_lt_1_plus_sqrt_6; lra. } assert (H7 : sqrt 6 - sqrt 2 - sqrt 3 < 0).
  { pose proof sqrt_2_plus_sqrt_3_minus_sqrt_6_gt_0; lra. } 
  destruct H5 as [n H5]. fold x in H6. fold x in H7.  assert (n < 0)%Z as H8. { apply lt_IZR. lra. }
  assert (n > - 1)%Z as H9. { apply Z.lt_gt. apply lt_IZR. lra. } lia.
Qed.

Lemma lemma_2_18_c : irrational (Rpower 2 (1/2) + Rpower 2 (1/3)).
Proof.
  set (x := Rpower 2 (1/2) + Rpower 2 (1/3)). assert (((x - (Rpower 2 (1/2)))^3 - 2) * ((x + (Rpower 2 (1/2)))^3 - 2) = 0) as H1.
  {
    unfold x. field_simplify. repeat rewrite <- Rpower_pow; try (apply Rpower_gt_0; lra).
    repeat rewrite Rpower_mult. replace (1/2 * INR 3) with (3/2) by (simpl; lra). replace (1/3 * INR 3) with (INR 1) by (simpl; lra).
    replace (1/2 * INR 2) with (INR 1) by (simpl; lra). 
    replace (1/3 * INR 5) with (5/3) by (simpl; lra). replace (1/3 * INR 2) with (2/3) by (simpl; lra).
    replace (1/3 * INR 6) with (INR 2) by (simpl; lra). repeat rewrite Rpower_pow; try lra. field_simplify.
    replace (6 * Rpower 2 (1 / 2) * Rpower 2 (5 / 3)) with (6 * Rpower 2 (INR 2 + 1 / 6)). 2 : { rewrite Rmult_assoc. rewrite <- Rpower_plus. replace (1/2 + 5/3) with (INR 2 + 1/6) by (simpl; lra). reflexivity. }
    replace (12 * Rpower 2 (1 / 2) * Rpower 2 (2 / 3)) with (12 * Rpower 2 (INR 1 + 1/6)). 2 : { rewrite Rmult_assoc. rewrite <- Rpower_plus. replace (1/2 + 2/3) with (INR 1 + 1/6) by (simpl; lra). reflexivity. }
    rewrite <- Rpower_mult. repeat rewrite Rpower_plus. repeat rewrite Rpower_pow; try apply Rpower_gt_0; try lra. field_simplify.
    replace (Rpower 2 (1/3) ^ 4) with (Rpower 2 (1/3) * Rpower 2 (1/3)^3) by reflexivity. rewrite <- Rpower_pow; try apply Rpower_gt_0; try lra. rewrite Rpower_mult. replace (1/3 * INR 3) with 1 by (simpl; lra).
    rewrite Rpower_1; lra.
  }
  assert (H2 : ((x - (Rpower 2 (1/2)))^3 - 2) * ((x + (Rpower 2 (1/2)))^3 - 2) = x^6 - 6 * x^4 - 4 * x^3 + 12 * x^2 - 24 * x - 4).
  {
    replace (Rpower 2 (1/2)) with (sqrt 2). 2 : { unfold Rdiv. rewrite Rmult_1_l. rewrite Rpower_sqrt; lra. }
    field_simplify. replace (sqrt 2 ^ 6) with (sqrt 2 ^2 * sqrt 2^4). 2 : { simpl. lra. } replace (sqrt 2 ^ 4) with (sqrt 2 ^2 * sqrt 2 ^ 2) by (simpl; lra). replace (sqrt 2 ^ 2) with 2. 2 : { rewrite pow2_sqrt; lra. }
    nra.
  }
  assert (H3 : sum_f 0 6 (fun i => IZR (nth i [-4; -24; 12; -4; -6; 0]%Z 1%Z) * x ^ i) = 0).
  { repeat rewrite sum_f_i_Sn_f; try rewrite sum_f_0_0; try lia. simpl. field_simplify. nra. }
  apply lemma_2_18_a in H3 as [H3 | H3]; auto.
  pose proof (sqrt_2_weak_bound) as H4. pose proof (cbrt_2_weak_bound) as H5. replace (sqrt 2) with (Rpower 2 (1/2)) in H4. 2 : { rewrite <- Rpower_sqrt; try lra. unfold Rdiv. rewrite Rmult_1_l. reflexivity. }
  assert (H6 : 2.6 < x < 2.8). { unfold x. nra. } assert (H7 : IZR 2 < x < IZR (2 + 1)) by (simpl; lra). apply (not_integer x 2%Z) in H7; tauto.
Qed.