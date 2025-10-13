From Lib Require Import Imports Binomial Sums.
Import Binomial_R Choose_R_Notations.
Open Scope R_scope.

Lemma lemma_2_3_a : forall n k : nat,
  (k >= 1)%nat -> (S n) ∁ k = n ∁ (k - 1) + n ∁ k.
Proof.
  intros. assert (H2 : (S n < k \/ S n = k \/ S n > k)%nat) by lia. destruct H2 as [H2 | [H2 | H2]].
  - repeat rewrite k_gt_n_n_choose_k. lra. lia. lia. lia.
  - assert (H3 : (n = k - 1)%nat) by lia. rewrite <- H3. rewrite H2. repeat rewrite n_choose_n.
    rewrite k_gt_n_n_choose_k. lra. lia.
  - unfold choose at 2.
    assert (H3 : (n >= k - 1)%nat) by lia. pose proof H3 as H4. apply nltb_ge in H4.
    rewrite H4. unfold choose at 2. assert (H5 : (n >= k)%nat) by lia. pose proof H5 as H6.
    apply nltb_ge in H6. rewrite H6. rewrite fact_div'. 2 : { lia. } 2 : { apply not_0_INR. apply fact_neq_0. }
    assert (H7: (n = k)%nat \/ (n > k)%nat) by lia. destruct H7 as [H7 | H7].
    -- rewrite H7. replace ((k - k)%nat) with 0%nat by lia. replace (k - (k - 1))%nat with (1)%nat by lia.
       simpl. repeat rewrite Rmult_1_r. unfold choose. assert (H8 : S k <? k = false). apply nltb_gt. lia.
       rewrite H8. replace (S k - k)%nat with 1%nat by lia. simpl. rewrite Rmult_1_r. rewrite plus_INR.
       rewrite mult_INR. nra.
    -- replace (n - k)%nat with (S (n - k) - 1)%nat by lia. rewrite Rmult_comm with (r2 := INR (fact (S (n - k) - 1))).
       rewrite fact_div' with (n := INR (fact n)).
       2 : { lia. } 2 : { apply not_0_INR. apply fact_neq_0. }
       replace (S (n - k))%nat with (n - (k - 1))%nat at 2 by lia.
       rewrite Rmult_comm with (r2 := INR (fact k)).
       replace (INR (fact n) * INR k / (INR (fact k) * INR (fact (n - (k - 1)))) + INR (fact n) * INR (S (n - k)) / (INR (fact k) * INR (fact (n - (k - 1))))) with
       ((INR (fact n) * INR k + INR (fact n) * INR (S (n - k))) / (INR (fact k) * INR (fact (n - (k - 1))))).
       2 : { nra. }
       rewrite <- Rmult_plus_distr_l. rewrite <- plus_INR. replace (k + S (n - k))%nat with (S n)%nat by lia.
       replace (INR (fact n) * INR (S n)) with (INR (fact (S n))). 2 : { rewrite <- mult_INR. simpl. replace (fact n * S n)%nat with (fact n + n * fact n)%nat by lia.
       reflexivity. }
       unfold choose. assert (H8 : S n <? k = false). apply nltb_gt. lia. rewrite H8.
       replace (n - (k - 1))%nat with (S n - k)%nat by lia. reflexivity.
Qed.

Lemma lemma_2_3_b : forall n k : nat,
  is_natural (n ∁ k).
Proof.
  intros n k. assert ((n < k \/ n = k \/ n > k)%nat) as [H1 | [H1 | H1]] by lia.
  - exists 0%nat. rewrite k_gt_n_n_choose_k; try lia. reflexivity.
  - exists 1%nat. rewrite H1. rewrite n_choose_n. reflexivity.
  - generalize dependent k. induction n as [| n' IH].
    -- intros n H1. exists 0%nat. rewrite O_choose_n; lia.
    -- intros n H1. assert (n = 0 \/ n >= 1)%nat as [H2 | H2] by lia.
       + rewrite H2. exists 1%nat. rewrite n_choose_0. reflexivity.
       + assert (n' = n \/ n' > n)%nat as [H3 | H3] by lia.
         * rewrite lemma_2_3_a; try lia. rewrite H3 at 2. rewrite n_choose_n. specialize (IH (n - 1)%nat). destruct IH as [m H4]; try lia.
           exists (m+1)%nat. rewrite H4. rewrite plus_INR. reflexivity.
         * rewrite lemma_2_3_a; try lia. pose proof IH as IH2. specialize (IH n). specialize (IH2 (n-1)%nat). destruct IH as [m H4]; try lia.
           destruct IH2 as [m' H5]; try lia. exists (m + m')%nat. rewrite H4. rewrite H5. rewrite plus_INR. lra.
Qed.

Lemma lemma_2_3_d : forall a b n,
  (a + b) ^ n = ∑ 0 n (fun i => (n ∁ i) * a ^ (n - i) * b ^ i).
Proof.
  intros a b n. induction n as [| k IH].
    - compute; lra.
    - replace ((a + b) ^ (S k)) with ((a + b) * (a + b) ^ k) by (simpl; lra).
      rewrite Rmult_plus_distr_r. repeat rewrite IH. repeat rewrite r_mult_sum_f_i_n_f.
      replace (fun i : nat => choose k i * a ^ (k - i) * b ^ i * a) with (fun i : nat => choose k i * a ^ (k - i + 1) * b ^ i).
      2 : { apply functional_extensionality. intros x. replace (choose k x * a ^ (k - x) * b ^ x * a) with (choose k x * (a ^ (k - x) * a) * b ^ x) by lra.
            replace (k - x + 1)%nat with (S (k - x))%nat by lia. rewrite <- tech_pow_Rmult. lra. }
      replace (fun i : nat => choose k i * a ^ (k - i) * b ^ i * b) with (fun i : nat => choose k i * a ^ (k - i) * b ^ (i + 1)).
      2 : { apply functional_extensionality. intros x. replace (choose k x * a ^ (k - x) * b ^ x * b) with (choose k x * a ^ (k - x) * (b ^ x * b)) by lra.
            replace (x + 1)%nat with (S x) by lia. rewrite <- tech_pow_Rmult. lra. }
      replace (sum_f 0 k (fun i : nat => choose k i * a ^ (k - i) * b ^ (i + 1))) with
      (sum_f 1 (k + 1) (fun i : nat => choose k (i-1) * a ^ (k - (i-1)) * b ^ (i))).
      2 : { rewrite sum_f_reindex' with (i := 0%nat) (n := k%nat) (s := 1%nat). simpl.
      set (f := fun i : nat => choose k (i - 1) * a ^ (k - (i - 1)) * b ^ i).
      set (g := fun x : nat => choose k (x - 1) * a ^ (k - (x - 1)) * b ^ (x - 1 + 1)).
      apply sum_f_equiv.
      - lia.
      - intros k0 H. unfold f, g. replace (k0 - 1 + 1)%nat with (k0) by lia. reflexivity. }
      destruct k as [| k'] eqn:Ek.
      -- compute. lra.
      -- rewrite sum_f_Si. 2 : { lia. }
        replace (S k' + 1)%nat with (S (k' + 1))%nat by lia.
        destruct k' as [| k''] eqn:Ek''.
        --- compute. lra.
        --- rewrite sum_f_i_Sn_f with (n := (S (k'' + 1))%nat). 2 : { lia. }
            repeat rewrite <- Ek. repeat replace ((S (k'' + 1))%nat) with (k)%nat by lia.
            replace (sum_f 1 k (fun i : nat => choose k i * a ^ (k - i + 1) * b ^ i) + choose k 0 * a ^ (k - 0 + 1) * b ^ 0 +
            (sum_f 1 k (fun i : nat => choose k (i - 1) * a ^ (k - (i - 1)) * b ^ i) + choose k (S k - 1) * a ^ (k - (S k - 1)) * b ^ S k))
            with (sum_f 1 k (fun i : nat => choose k i * a ^ (k - i + 1) * b ^ i) + sum_f 1 k (fun i : nat => choose k (i - 1) * a ^ (k - (i - 1)) * b ^ i) +
            choose k 0 * a ^ (k - 0 + 1) * b ^ 0 + choose k (S k - 1) * a ^ (k - (S k - 1)) * b ^ S k) by lra.
            rewrite sum_f_sum. assert (H2 : sum_f 1 k (fun x : nat => choose k x * a ^ (k - x + 1) * b ^ x + choose k (x - 1) * a ^ (k - (x - 1)) * b ^ x)
            = sum_f 1 k (fun x : nat => choose (S k) x * a ^ (k - x + 1) * b ^ x)).
            { apply sum_f_equiv. lia. intros k0 H2. replace (k - (k0 - 1))%nat with (k - k0 + 1)%nat by lia.
            rewrite Rmult_assoc. rewrite Rmult_assoc with (r1 := choose k (k0 - 1)) at 1.
            rewrite <- Rmult_plus_distr_r with (r3 := a ^ (k - k0 + 1) * b ^ k0). rewrite Rplus_comm. rewrite binomial_recursion_R_1. 2 : { lia. } lra. }
            rewrite H2. rewrite sum_f_Si_n_f. 2 : { lia. } rewrite sum_f_i_Sn_f. 2 : { lia. } replace (choose (S k) (S k)) with 1. 2 : { rewrite n_choose_n. auto. }
            replace (choose (S k) 0%nat) with 1. 2 : { rewrite n_choose_0. reflexivity. }
            repeat rewrite Rmult_1_l. replace (k - (S k - 1))%nat with 0%nat by lia. replace (S k - S k)%nat with 0%nat by lia.
            replace (b ^ 0) with 1 by auto. replace (a ^ 0) with 1 by auto. rewrite Rmult_1_l. repeat rewrite Rmult_1_r.
            replace (k - 0 + 1)%nat with (S k) by lia. replace (S k - 1)%nat with k%nat by lia. rewrite n_choose_n. rewrite Rmult_1_l. rewrite n_choose_0.
            rewrite Rmult_1_l. replace (sum_f 0 k (fun x : nat => choose (S k) x * a ^ (k - x + 1) * b ^ x)) with (sum_f 0 k (fun i : nat => choose (S k) i * a ^ (S k - i) * b ^ i)).
            2 : { apply sum_f_equiv. lia. intros k0 H3. replace (S k - k0)%nat with (k - k0 + 1)%nat by lia. reflexivity. }
            nra.
Qed.

Lemma lemma_2_3_e_i : forall n,
  ∑ 0 n (fun j => n ∁ j) = 2 ^ n.
Proof.
  intros n. replace 2 with (1 + 1) by lra.
  rewrite lemma_2_3_d. apply sum_f_equiv; try lia.
  intros k H1. repeat rewrite pow1. lra.
Qed.

Lemma lemma_2_3_e_ii : forall n, 
  (n >= 1)%nat ->
    ∑ 0 n (fun j => (-1) ^ j * (n ∁ j)) = 0.
Proof.
  intros n H1. replace 0 with ((1 + -1)^n). 2 : { replace (1 + -1) with 0 by lra. rewrite pow_ne_zero; auto. lia. }
  rewrite lemma_2_3_d. apply sum_f_equiv; try lia. intros k H2. rewrite pow1. lra.
Qed.

Lemma odd_spec_false : forall n : nat,
  Nat.odd n = false -> Nat.even n = true.
Proof.
  intros n H1. pose proof Nat.orb_even_odd n as H2. apply orb_prop in H2 as [H2 | H2]; auto.
  assert (true = false) as H3. rewrite <- H1, H2. reflexivity. inversion H3.
Qed.

Lemma even_spec_false : forall n : nat,
  Nat.even n = false -> Nat.odd n = true.
Proof.
  intros n H1. pose proof Nat.orb_even_odd n as H2. apply orb_prop in H2 as [H2 | H2]; auto.
  assert (true = false) as H3. rewrite <- H1, H2. reflexivity. inversion H3.
Qed.

Lemma lemma_2_3_e_iii : forall n,
  (n >= 1)%nat -> ∑ 0 n (fun l => if Nat.odd l then n ∁ l else 0) = 2 ^ (n - 1).
Proof.
  intros n H1. assert (H2 : 2 * sum_f 0 n (fun l => if Nat.odd l then choose n l else 0) = sum_f 0 n (fun j => choose n j) - sum_f 0 n (fun j => (-1) ^ j * choose n j)).
  - rewrite sum_f_minus; try lia. rewrite r_mult_sum_f_i_n_f. apply sum_f_equiv; try lia. intros k H2. destruct (Nat.odd k) eqn:H3.
    -- rewrite Nat.odd_spec in H3. destruct H3 as [m H3]. replace (2 * m + 1)%nat with (S (2 * m)) in H3 by lia. rewrite H3 at 3. rewrite pow_1_odd. lra.
    -- pose proof Nat.orb_even_odd n as H4. assert (H5 : Nat.even k = true) by (apply odd_spec_false; auto). rewrite Nat.even_spec in H5. destruct H5 as [m H5]. rewrite H5. rewrite pow_1_even. lra.
  - apply Rmult_eq_compat_l with (r := / 2) in H2. rewrite <- Rmult_assoc in H2. rewrite Rinv_l in H2; try lra. rewrite Rmult_1_l in H2. rewrite H2. rewrite lemma_2_3_e_i. rewrite lemma_2_3_e_ii; try lia.
    rewrite Rminus_0_r. replace n%nat with (S (n-1))%nat at 1 by lia. simpl. lra.
Qed.

Lemma lemma_2_3_e_iv : forall n,
  (n >= 1)%nat -> ∑ 0 n (fun l => if Nat.even l then n ∁ l else 0) = 2 ^ (n - 1).
Proof.
  intros n H1. assert (H2 : 2 * sum_f 0 n (fun l => if Nat.even l then choose n l else 0) = sum_f 0 n (fun j => choose n j) + sum_f 0 n (fun j => (-1) ^ j * choose n j)).
  - rewrite sum_f_plus; try lia. rewrite r_mult_sum_f_i_n_f. apply sum_f_equiv; try lia. intros k H2. destruct (Nat.even k) eqn:H3.
    -- rewrite Nat.even_spec in H3. destruct H3 as [m H3]. rewrite H3. rewrite pow_1_even. lra.
    -- pose proof Nat.orb_even_odd n as H4. assert (H5 : Nat.odd k = true) by (apply even_spec_false; auto). rewrite Nat.odd_spec in H5. destruct H5 as [m H5].
       replace (2 * m + 1)%nat with (S (2 * m)) in H5 by lia. rewrite H5 at 2. rewrite pow_1_odd. lra. 
  - apply Rmult_eq_compat_l with (r := / 2) in H2. rewrite <- Rmult_assoc in H2. rewrite Rinv_l in H2; try lra. rewrite Rmult_1_l in H2. rewrite H2. rewrite lemma_2_3_e_i. rewrite lemma_2_3_e_ii; try lia.
    rewrite Rplus_0_r. replace n%nat with (S (n-1))%nat at 1 by lia. simpl. lra.
Qed.