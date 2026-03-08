From Calculus.Chapter2 Require Import Prelude Problem_2_8.

Open Scope Z_scope.

Lemma lemma_2_17_a : forall z : Z,
  z > 1 -> exists l : list Z,
    prime_list l /\ z = fold_right Z.mul 1 l.
Proof.
  intros z. assert (z <= 1 \/ z > 1) as [H1 | H1]; try lia.
  apply strong_induction_Z with (n := z); try lia.
  intros n IH H2. assert (n = 2 \/ n > 2) as [H3 | H3] by lia.
  - exists [2]. split; simpl; auto. right; auto. apply Znt.prime_2.
  - destruct (Znt.prime_dec n) as [H4 | H4].
    + exists [n]. split; simpl; try lia; constructor; auto.
    + rewrite <- Znt.prime_alt in H4. unfold Znt.prime' in H4. apply not_and_or in H4 as [H4 | H4]; try lia.
      apply not_all_ex_not in H4 as [p H4]. apply imply_to_and in H4 as [H4 H5].
      apply NNPP in H5. destruct H5 as [k H5]. assert (p > 1 /\ 0 <= p < n) as [H7 H8] by lia.
      assert (k > 1 /\ 0 <= k < n) as [H9 H10] by nia.
      assert (exists l1 : list Z, prime_list l1 /\ p = fold_right Z.mul 1 l1) as [l1 H11] by (apply IH; lia).
      assert (exists l2 : list Z, prime_list l2 /\ k = fold_right Z.mul 1 l2) as [l2 H12] by (apply IH; lia).
      exists (l1 ++ l2). split.
      -- apply Forall_app. split; [apply H11 | apply H12].
      -- destruct H11 as [H11 H13]. destruct H12 as [H12 H14]. rewrite fold_right_app. rewrite <- H14.
        rewrite fold_right_mul_distributive. rewrite <- H13. lia.
Qed.

Lemma lemma_2_17_b : forall n : Z,
  (n >= 0)%Z ->
  (~(exists m, (n = m^2))%Z) -> irrational (sqrt (IZR n)).
Proof.
  intros n H1 H2 [a [b H3]]. unfold not in *. apply H2. assert (n = 0 \/ n > 0) as [H4 | H4] by lia.
  - exists 0. lia.
  - clear H1. rename H4 into H1.
    assert (Rsqr (sqrt (IZR n)) = Rsqr (IZR a / IZR b)) as H4 by (rewrite H3; reflexivity).
    rewrite Rsqr_def in H4. rewrite sqrt_def in H4. 2 : { apply IZR_le; lia. }
    assert (IZR n * IZR b ^ 2 = IZR a ^ 2)%R as H5.
    { 
      rewrite H4. repeat rewrite Rsqr_def. field. apply not_0_IZR. assert (b = 0 \/ b <> 0) as [H5 | H5] by lia; auto.
      rewrite H5 in H4. unfold Rdiv in H4. rewrite Rinv_0 in H4. rewrite Rmult_0_r in H4. rewrite Rsqr_def in H4. rewrite Rmult_0_r in H4.
      apply eq_IZR_R0 in H4. lia. 
    }
    repeat rewrite pow_IZR in H5. rewrite <- mult_IZR in H5. apply eq_IZR in H5. replace (Z.of_nat 2) with 2%Z in H5 by reflexivity.
    assert (n = 1 \/ n > 1) as [H6 | H6] by lia; try (exists 1; lia). clear H1. rename H6 into H1. 
    assert (a <> 0 /\ b <> 0) as [H6 H7].
    {
      split.
        - intros H6. rewrite H6 in H4. unfold Rdiv in H4. rewrite Rmult_0_l in H4. rewrite Rsqr_def in H4. rewrite Rmult_0_l in H4. 
          apply eq_IZR_R0 in H4. lia.
        - intros H6. rewrite H6 in H4. unfold Rdiv in H4. rewrite Rinv_0 in H4. rewrite Rmult_0_r in H4. rewrite Rsqr_def in H4. rewrite Rmult_0_r in H4.
          apply eq_IZR_R0 in H4. lia.
    }
    assert (b = 1 \/ b = -1 \/ (b < -1 \/ b > 1)) as [H8 | [H8 | [H8 | H8]]] by lia; try (exists a; lia).
    -- assert (a = 1 \/ a = -1 \/ (a < -1 \/ a > 1)) as [H9 | [H9 | [H9 | H9]]] by lia; try lia.
       + pose proof (lemma_2_17_a n H1) as [l1 [H10 H11]]. pose proof (prime_list_product_exists_neg a H9) as [l2 [H12 H13]].
         pose proof (prime_list_product_exists_neg b H8) as [l3 [H14 H15]]. 
         assert (H16 : -a > 1) by lia. clear H9. rename H16 into H9. assert (H16 : -b > 1) by lia. clear H8. rename H16 into H8.
         pose proof (z_square_even_primes (-a) H9) as [l4 [H16 [H17 H18]]]. replace ((-a)^2) with (a^2) in H17 by lia.
         pose proof (z_square_even_primes (-b) H8) as [l5 [H19 [H20 H21]]]. replace ((-b)^2) with (b^2) in H20 by lia.
         rewrite H20 in H5. rewrite H17 in H5. clear H17 H20. apply even_count_occ_perfect_square. exists l1. split; auto.
         intros p. specialize (H18 p). specialize (H21 p). rewrite H11 in H5. rewrite <- fold_right_mult_app_Z in H5.
         assert (H22 : prime_list (l1 ++ l5)) by (apply prime_list_app; tauto).
         pose proof (prime_factorization_unique (l1 ++ l5) l4 (fold_right Z.mul 1 (l1 ++ l5)) p H22 H16 eq_refl H5) as H23.
         rewrite count_occ_app in H23. assert (Nat.Even (count_occ Z.eq_dec l1 p + count_occ Z.eq_dec l5 p)) as H24 by (rewrite H23; auto).
         apply Nat.Even_add_Even_inv_l with (m := count_occ Z.eq_dec l5 p) in H24; auto.
       + pose proof (lemma_2_17_a n H1) as [l1 [H10 H11]]. pose proof (prime_list_product_exists_pos a H9) as [l2 [H12 H13]].
         pose proof (prime_list_product_exists_neg b H8) as [l3 [H14 H15]]. 
         assert (H16 : -b > 1) by lia. clear H8. rename H16 into H8. pose proof (z_square_even_primes (-b) H8) as [l4 [H16 [H17 H18]]].
         pose proof (z_square_even_primes a H9) as [l5 [H19 [H20 H21]]]. rewrite H20 in H5. clear H20 H15.
         replace ((-b)^2) with (b^2) in H17 by lia. rewrite H17 in H5. clear H17. apply even_count_occ_perfect_square. exists l1. split; auto.
         intros p. specialize (H18 p). specialize (H21 p). rewrite H11 in H5. rewrite <- fold_right_mult_app_Z in H5. assert (H17 : prime_list (l1 ++ l4)) by (apply prime_list_app; tauto).
         pose proof (prime_factorization_unique (l1 ++ l4) l5 (fold_right Z.mul 1 (l1 ++ l4)) p H17 H19 eq_refl) as H22. rewrite count_occ_app in H22.
         assert (Nat.Even (count_occ Z.eq_dec l1 p + count_occ Z.eq_dec l4 p)) as H23 by (rewrite H22; auto). apply Nat.Even_add_Even_inv_l with (m := count_occ Z.eq_dec l4 p) in H23; auto.
    -- assert (a = 1 \/ a = -1 \/ (a < -1 \/ a > 1)) as [H9 | [H9 | [H9 | H9]]] by lia; try lia.
       + pose proof (lemma_2_17_a n H1) as [l1 [H10 H11]]. pose proof (prime_list_product_exists_neg a H9) as [l2 [H12 H13]].
         pose proof (prime_list_product_exists_pos b H8) as [l3 [H14 H15]]. 
         assert (H16 : -a > 1) by lia. clear H9. rename H16 into H9. pose proof (z_square_even_primes (-a) H9) as [l4 [H16 [H17 H18]]].
         pose proof (z_square_even_primes b H8) as [l5 [H19 [H20 H21]]]. rewrite H20 in H5. clear H20 H13.
         replace ((-a)^2) with (a^2) in H17 by lia. rewrite H17 in H5. clear H17. apply even_count_occ_perfect_square. exists l1. split; auto.
         intros p. specialize (H18 p). specialize (H21 p). rewrite H11 in H5. rewrite <- fold_right_mult_app_Z in H5. assert (H17 : prime_list (l1 ++ l5)) by (apply prime_list_app; tauto).
         pose proof (prime_factorization_unique (l1 ++ l5) l4 (fold_right Z.mul 1 (l1 ++ l5)) p H17 H16 eq_refl) as H22. rewrite count_occ_app in H22.
         assert (Nat.Even (count_occ Z.eq_dec l1 p + count_occ Z.eq_dec l5 p)) as H23 by (rewrite H22; auto). apply Nat.Even_add_Even_inv_l with (m := count_occ Z.eq_dec l5 p) in H23; auto.
       + pose proof (lemma_2_17_a n H1) as [l1 [H10 H11]]. pose proof (prime_list_product_exists_pos a H9) as [l2 [H12 H13]].
         pose proof (prime_list_product_exists_pos b H8) as [l3 [H14 H15]]. 
         pose proof (z_square_even_primes a H9) as [l4 [H16 [H17 H18]]]. pose proof (z_square_even_primes b H8) as [l5 [H19 [H20 H21]]].
         rewrite H20 in H5. rewrite H17 in H5. clear H20 H17. apply even_count_occ_perfect_square. exists l1. split; auto.
         intros p. specialize (H18 p). specialize (H21 p). rewrite H11 in H5. rewrite <- fold_right_mult_app_Z in H5. assert (H20 : prime_list (l1 ++ l5)) by (apply prime_list_app; tauto).
         pose proof (prime_factorization_unique (l1 ++ l5) l4 (fold_right Z.mul 1 (l1 ++ l5)) p H20 H16 eq_refl) as H22. rewrite count_occ_app in H22.
         assert (Nat.Even (count_occ Z.eq_dec l1 p + count_occ Z.eq_dec l5 p)) as H23 by (rewrite H22; auto). apply Nat.Even_add_Even_inv_l with (m := count_occ Z.eq_dec l5 p) in H23; auto.
Qed.

Lemma lemma_2_17_c : forall n k,
  (n > 0)%Z -> (k > 0)%nat -> 
  ((~exists m, (n = m^Z.of_nat k)%Z) -> irrational (Rpower (IZR n) (1 / INR k))).
Proof.
  intros n k H1 H2 H3. unfold not in *. intros [a [b H4]]. apply H3.
  assert (Rpower (IZR n) (1 / INR k) ^ k = (IZR a / IZR b) ^ k)%R as H5 by (rewrite H4; reflexivity).
  assert (n = 1 \/ n > 1)%Z as [H0 | H0] by lia.
  exists 1. rewrite Z.pow_1_l; lia.
  assert (a <> 0 /\ b <> 0) as [H6 H7].
  {
    split.
    - intros H6. rewrite H6 in H4. unfold Rdiv in H4. rewrite Rmult_0_l in H4. 
      assert (Rpower (IZR n) (1 * / INR k) > 0)%R by (apply Rpower_gt_0; apply IZR_lt; lia). lra.
    - intros H6. rewrite H6 in H4. unfold Rdiv in H4. rewrite Rinv_0 in H4. rewrite Rmult_0_r in H4.
      assert (Rpower (IZR n) (1 * / INR k) > 0)%R by (apply Rpower_gt_0; apply IZR_lt; lia). lra.
  }
  assert (IZR n * IZR b ^ k = IZR a ^ k)%R as H8.
  {
    rewrite <- Rpower_pow in H5. 2 : { apply Rpower_gt_0. apply IZR_lt. lia. }
    rewrite Rpower_mult in H5. replace (1 / INR k * INR k)%R with 1%R in H5. 2 : { field. apply not_0_INR. lia. }
    rewrite Rpower_1 in H5. 2 : { apply IZR_lt. lia. } rewrite Rpow_div_l in H5. 2 : { apply not_0_IZR. lia. }
    2 : { apply not_0_IZR. lia. } rewrite H5. field. apply Rpow_neq_0. apply not_0_IZR. lia.
  }
  rewrite pow_IZR in H8. rewrite <- mult_IZR in H8. rewrite pow_IZR in H8. apply eq_IZR in H8.
  assert (b = 1 \/ b = -1 \/ (b < -1 \/ b > 1)) as [H9 | [H9 | [H9 | H9]]] by lia.
  - rewrite H9 in H8. rewrite Z.pow_1_l in H8. exists a. lia. lia. 
  - rewrite H9 in H8. assert (Nat.Even k \/ Nat.Odd k) as [H10 | H11] by apply lemma_2_8.
    + exists a. rewrite Zpow_neg1_nat_even in H8; auto. lia.
    + assert (a = 1 \/ a = -1 \/ (a < -1 \/ a > 1)) as [H12 | [H12 | [H12 | H12]]] by lia.
      * rewrite H12 in H8. exists (-1). rewrite Zpow_neg1_nat_odd in *; auto. rewrite Z.pow_1_l in H8; lia.
      * rewrite H12 in H8. exists 1. rewrite Z.pow_1_l; try lia. rewrite Zpow_neg1_nat_odd in H8; auto. lia.
      * exists (-a). rewrite Zpow_neg1_nat_odd in H8; auto. rewrite Z.pow_opp_odd. 2 : { apply Odd_ZOdd; auto. } lia.
      * exists (-a). rewrite Zpow_neg1_nat_odd in H8; auto. rewrite Z.pow_opp_odd. 2 : { apply Odd_ZOdd; auto. } lia.
  - assert (a = 1 \/ a = -1 \/ (a < -1 \/ a > 1)) as [H10 | [H10 | [H10 | H10]]] by lia.
    + rewrite H10 in H8. exists 1. rewrite Z.pow_1_l; try lia. rewrite Z.pow_1_l in H8; try lia. apply Zmult_eq_1 in H8 as [[H11 H12] | [H11 H12]]; lia.
    + rewrite H10 in H8. assert (Nat.Even k \/ Nat.Odd k) as [H11 | H12] by apply lemma_2_8.
      * exists 1. rewrite Z.pow_1_l; try lia. rewrite Zpow_neg1_nat_even in H8; auto. apply Zmult_eq_1 in H8 as [[H13 H14] | H13]; lia.
      * exists 1. rewrite Z.pow_1_l; try lia. rewrite Zpow_neg1_nat_odd in H8; auto. apply Zmult_eq_neg1 in H8 as [[H13 H14] | H13]; lia. 
    + pose proof (lemma_2_17_a n H0) as [l1 [H11 H12]]. pose proof (prime_list_product_exists_neg a H10) as [l2 [H13 H14]].
      pose proof (prime_list_product_exists_neg b H9) as [l3 [H15 H16]]. 
      assert (-a > 1) as H17 by lia. clear H10. rename H17 into H10. assert (-b > 1) as H17 by lia. clear H9. rename H17 into H9.
      pose proof (z_pow_factor_primes (-a) k H10) as [l4 [H17 [H18 H19]]]. pose proof (z_pow_factor_primes (-b) k H9) as [l5 [H20 [H21 H22]]].
      apply count_occ_perfect_factor. exists l1. split; auto. intros p. specialize (H19 p). specialize (H22 p). destruct H19 as [q1 H19]. destruct H22 as [q2 H22]. 
      assert (H23 : Nat.Even k \/ Nat.Odd k) by apply lemma_2_8. destruct H23 as [H23 | H23].
      * rewrite Zpow_neg_nat_even in H18, H21; auto. rewrite H18 in H8. rewrite H21 in H8. rewrite H12 in H8. rewrite <- fold_right_mult_app_Z in H8.
        assert (H24 : prime_list (l1 ++ l5)) by (apply prime_list_app; tauto). pose proof (prime_factorization_unique (l1 ++ l5) l4 (fold_right Z.mul 1 (l1 ++ l5)) p H24 H17 eq_refl H8) as H25.
        rewrite count_occ_app in H25.  rewrite H19 in H25. rewrite H22 in H25. exists (q1 - q2)%nat. nia.
      * rewrite Zpow_neg_nat_odd in H18, H21; auto. assert (H24 : n * fold_right Z.mul 1 l5 = fold_right Z.mul 1 l4) by lia. clear H8. rename H24 into H8. rewrite H12 in H8.
        rewrite <- fold_right_mult_app_Z in H8. assert (H24 : prime_list (l1 ++ l5)) by (apply prime_list_app; tauto). pose proof (prime_factorization_unique (l1 ++ l5) l4 (fold_right Z.mul 1 (l1 ++ l5)) p H24 H17 eq_refl H8) as H25.
        rewrite count_occ_app in H25.  rewrite H19 in H25. rewrite H22 in H25. exists (q1 - q2)%nat. nia.
    + pose proof (lemma_2_17_a n H0) as [l1 [H11 H12]]. pose proof (prime_list_product_exists_pos a H10) as [l2 [H13 H14]].
      pose proof (prime_list_product_exists_neg b H9) as [l3 [H15 H16]]. 
      assert (-b > 1) as H17 by lia. clear H9. rename H17 into H9. pose proof (z_pow_factor_primes (-b) k H9) as [l4 [H17 [H18 H19]]].
      pose proof (z_pow_factor_primes a k H10) as [l5 [H20 [H21 H22]]]. rewrite H21 in H8. assert (Nat.Even k \/ Nat.Odd k) as [H23 | H23] by apply lemma_2_8.
      * rewrite Zpow_neg_nat_even in H18; auto. rewrite H18 in H8. rewrite H12 in H8. rewrite <- fold_right_mult_app_Z in H8. assert (H24 : prime_list (l1 ++ l4)) by (apply prime_list_app; tauto).
        apply count_occ_perfect_factor. exists l1. split; auto. intros p. specialize (H19 p). specialize (H22 p). destruct H19 as [q1 H19]. destruct H22 as [q2 H22].
        pose proof (prime_factorization_unique (l1 ++ l4) l5 (fold_right Z.mul 1 (l1 ++ l4)) p H24 H20 eq_refl) as H25. exists (q2 - q1)%nat. rewrite count_occ_app in H25. nia.
      * rewrite Zpow_neg_nat_odd in H18; auto. assert (H24 : n * fold_right Z.mul 1 l4 = -fold_right Z.mul 1 l5) by lia. clear H8. rename H24 into H8. rewrite H12 in H8.
        rewrite <- fold_right_mult_app_Z in H8. assert (H24 : prime_list (l1 ++ l4)) by (apply prime_list_app; tauto). pose proof (prime_list_fold_right_pos (l1 ++ l4) H24) as H25.
        pose proof (prime_list_fold_right_pos l5 H20) as H26. nia.
    - assert (a = 1 \/ a = -1 \/ (a < -1 \/ a > 1)) as [H10 | [H10 | [H10 | H10]]] by lia.
      + rewrite H10 in H8. exists 1. rewrite Z.pow_1_l; try lia. rewrite Z.pow_1_l in H8; try lia.
      + rewrite H10 in H8. assert (Nat.Even k \/ Nat.Odd k) as [H11 | H12] by apply lemma_2_8.
        * exists 1. rewrite Z.pow_1_l; try lia. rewrite Zpow_neg1_nat_even in H8; auto. apply Zmult_eq_1 in H8 as [[H13 H14] | H13]; lia.
        * exists 1. rewrite Z.pow_1_l; try lia. rewrite Zpow_neg1_nat_odd in H8; auto. apply Zmult_eq_neg1 in H8 as [[H13 H14] | H13]; lia. 
      + pose proof (lemma_2_17_a n H0) as [l1 [H11 H12]]. pose proof (prime_list_product_exists_neg a H10) as [l2 [H13 H14]].
        pose proof (prime_list_product_exists_pos b H9) as [l3 [H15 H16]]. 
        assert (-a > 1) as H17 by lia. clear H10. rename H17 into H10.
        pose proof (z_pow_factor_primes (-a) k H10) as [l4 [H17 [H18 H19]]]. pose proof (z_pow_factor_primes b k H9) as [l5 [H20 [H21 H22]]].
        apply count_occ_perfect_factor. exists l1. split; auto. intros p. specialize (H19 p). specialize (H22 p). destruct H19 as [q1 H19]. destruct H22 as [q2 H22]. 
        assert (Nat.Even k \/ Nat.Odd k) as [H23 | H23] by apply lemma_2_8.
        * rewrite Zpow_neg_nat_even in H18; auto. rewrite H18 in H8. rewrite H21 in H8. rewrite H12 in H8. rewrite <- fold_right_mult_app_Z in H8.
          assert (H24 : prime_list (l1 ++ l5)) by (apply prime_list_app; tauto). pose proof (prime_factorization_unique (l1 ++ l5) l4 (fold_right Z.mul 1 (l1 ++ l5)) p H24 H17 eq_refl H8) as H25.
          rewrite count_occ_app in H25.  rewrite H19 in H25. rewrite H22 in H25. exists (q1 - q2)%nat. nia.
        * rewrite Zpow_neg_nat_odd in H18; auto. assert (H24 : prime_list (l1 ++ l5)) by (apply prime_list_app; tauto). pose proof (prime_list_fold_right_pos (l1 ++ l5) H24) as H25.
          pose proof (prime_list_fold_right_pos l4 H17) as H26. nia.
      + pose proof (lemma_2_17_a n H0) as [l1 [H11 H12]]. pose proof (prime_list_product_exists_pos a H10) as [l2 [H13 H14]]. 
        pose proof (prime_list_product_exists_pos b H9) as [l3 [H15 H16]]. apply count_occ_perfect_factor. exists l1. split; auto.
        intros p. rewrite H12 in H8. pose proof (z_pow_factor_primes a k H10) as [l4 [H17 [H18 H19]]]. pose proof (z_pow_factor_primes b k H9) as [l5 [H20 [H21 H22]]].
        specialize (H19 p). specialize (H22 p). destruct H19 as [q1 H19]. destruct H22 as [q2 H22]. rewrite H21 in H8. rewrite H18 in H8. rewrite <- fold_right_mult_app_Z in H8. 
        assert (H23 : prime_list (l1 ++ l5)) by (apply prime_list_app; tauto). pose proof (prime_factorization_unique (l1 ++ l5) l4 (fold_right Z.mul 1 (l1 ++ l5)) p H23 H17 eq_refl H8) as H24.
        rewrite count_occ_app in H24.  rewrite H19 in H24. rewrite H22 in H24. exists (q1 - q2)%nat. nia.
Qed.

Lemma lemma_2_17_d : forall (l : list Z),
  first_n_primes l -> exists p : Z, Znt.prime p /\ p > max_list_Z l.
Proof.
  intros l [H1 [H2 H3]]. set (N := fold_right Z.mul 1 l + 1).
  assert (N > 1) as H4 by (destruct l; apply prime_list_product_gt_1 in H2; lia).
  destruct (prime_divides N H4) as [q H5]. exists q. split.
  - apply Znt.prime_alt. apply H5.
  - destruct H5 as [H5 H6]. apply Znt.prime_alt in H5. destruct (in_dec Z.eq_dec q l) as [H7 | H7].
    -- assert ((q | fold_right Z.mul 1 l)) as H8 by (apply fold_right_factor_divides; auto).
       unfold N in H6. pose proof (prime_no_div q (fold_right Z.mul 1 l) H5 H8 H6) as H9. lia.
    -- specialize (H3 q). tauto.
Qed.