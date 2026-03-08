From Calculus.Chapter2 Require Import Prelude.

Module Znt := ZArith.Znumtheory.

Open Scope R_scope.

Theorem sum_n_nat : forall n : nat,
  (n >= 1)%nat -> sum_f 1 n (fun i => INR i) = (INR n * (INR n + 1)) / 2.
Proof.
  intros n H1. induction n as [| k IH]; try lia. assert (S k = 1 \/ k >= 1)%nat as [H2 | H2] by lia.
  - rewrite H2. compute. lra.
  - rewrite sum_f_i_Sn_f; try lia. rewrite IH; auto. rewrite S_INR. lra.
Qed.

Lemma lemma_2_1_i : forall n : nat,
  (n >= 1)%nat -> sum_f 1 n (fun i => INR i ^ 2) = (INR n * (INR n + 1) * (2 * INR n + 1)) / 6.
Proof.
  intros n H1. induction n as [| k IH]; try lia. assert (S k = 1 \/ k >= 1)%nat as [H2 | H2] by lia.
  - rewrite H2. compute. lra.
  - rewrite sum_f_i_Sn_f; try lia. rewrite IH; auto. rewrite S_INR. lra.
Qed.

Lemma lemma_2_1_ii : forall n : nat,
  (n >= 1)%nat -> sum_f 1 n (fun i => INR i ^ 3) = (sum_f 1 n (fun i => INR i)) ^ 2.
Proof.
  intros n H1. induction n as [| k IH]; try lia. assert (S k = 1 \/ k >= 1)%nat as [H2 | H2] by lia.
  - rewrite H2. compute. lra.
  - repeat rewrite sum_f_i_Sn_f; try lia. rewrite IH; auto. rewrite sum_n_nat; auto. repeat rewrite S_INR. lra.  
Qed.

Lemma lemma_2_2_i : forall n : nat,
  (n >= 1)%nat -> sum_f 1 n (fun i => 2 * (INR i) - 1) = INR (n^2).
Proof.
  intros n H. induction n as [| k IH].
  - lia.
  - assert (k = 0 \/ k = 1 \/ k > 1)%nat as [H1 | [H1 | H1]] by lia.
    -- rewrite H1. compute. lra.
    -- rewrite H1. compute. lra.
    -- assert (k >= 1)%nat as H2 by lia. apply IH in H2. rewrite sum_f_i_Sn_f. 2 : { lia. }
       rewrite H2. replace (S k ^ 2)%nat with (k^2 + 2 * k + 1)%nat. 2 : { simpl. repeat rewrite Nat.mul_1_r. lia. }
       replace (k^2 + 2 * k + 1)%nat with (k^2 + (2 * k + 1))%nat by lia. rewrite plus_INR.
       replace (2 * INR (S k) - 1) with (INR (2 * k + 1)).
       2 : { rewrite S_INR. repeat rewrite plus_INR. rewrite mult_INR. simpl. lra. }
       lra.
Qed.

Lemma lemma_2_2_ii : forall n : nat,
  (n >= 1)%nat -> sum_f 1 n (fun i => (2 * INR i - 1)^2) = INR n * (2 * INR n + 1) * (2 * INR n - 1) / 3.
Proof.
  intros n H. induction n as [| k IH].
  - lia.
  - assert (k = 0 \/ k = 1 \/ k > 1)%nat as [H1 | [H1 | H1]] by lia.
    -- rewrite H1. compute. lra.
    -- rewrite H1. compute. lra.
    -- assert (k >= 1)%nat as H2 by lia. apply IH in H2. rewrite sum_f_i_Sn_f. 2 : { lia. }
       rewrite H2. replace (INR (S k)) with (INR k + 1). 2 : { rewrite S_INR. auto. }
       field.
Qed.

Definition choose (n k : nat) : R :=
  if (n <? k) then 0 else
  (INR (fact n)) / (INR (fact k) * INR (fact (n - k))).

Lemma n_choose_n : forall (n : nat),
  choose n n = 1.
Proof.
  intro n. unfold choose. replace (n - n)%nat with 0%nat by lia.
  simpl. rewrite Rmult_1_r. rewrite Nat.ltb_irrefl.
  field. apply INR_fact_neq_0.
Qed.

Lemma Sn_choose_n : forall (n : nat),
  choose (S n) n = INR (S n).
Proof.
  intro n. unfold choose. assert (S n <? n = false) as H1. apply Nat.ltb_ge. lia. rewrite H1. replace (S n - n)%nat with 1%nat by lia.
  replace (fact 1) with 1%nat by reflexivity. replace (fact (S n)) with ((S n) * fact n)%nat. 2 : { simpl. reflexivity. }
  rewrite mult_INR. unfold Rdiv. rewrite Rmult_assoc. field_simplify. replace (INR 1) with 1 by reflexivity. nra. split. apply not_0_INR. lia. apply not_0_INR.
  apply fact_neq_0.
Qed.

Lemma n_choose_0 : forall (n : nat),
  choose n 0 = 1.
Proof.
  intro n. unfold choose. simpl. rewrite Nat.sub_0_r. rewrite Rmult_1_l.
  field. apply INR_fact_neq_0.
Qed.

Lemma O_choose_n : forall (n : nat),
  (n <> 0)%nat -> choose 0 n = 0.
Proof.
  intros n H1. unfold choose. simpl. destruct n; try lia; simpl. lra.
Qed.

Lemma k_gt_n_n_choose_k : forall n k : nat,
  (n < k)%nat -> choose n k = 0.
Proof.
  intros. assert (H2 : n <? k = true).
  { apply Nat.ltb_lt. apply H. }
  unfold choose. rewrite H2. reflexivity.
Qed.

Lemma nltb_gt : forall a b : nat, (a > b)%nat -> (a <? b) = false.
Proof.
  intros a b H. induction b.
  - auto.
  - unfold "<?". apply leb_correct_conv. lia.
Qed.

Lemma nltb_ge : forall a b : nat, (a >= b)%nat -> (a <? b) = false.
Proof.
  intros a b H. induction b.
  - auto.
  - unfold "<?". apply leb_correct_conv. lia.
Qed.

Lemma fact_div : forall m n k,
  (k >= 1)%nat -> (m <> 0) -> n / ((INR (fact (k - 1))) * m)  = (n * INR (k)) / (INR (fact k) * m).
Proof.
  intros m n k H1 H2. destruct k.
  - lia.
  - destruct k.
    -- simpl. lra.
    -- replace (fact (S (S k))) with ((S (S k)) * fact (S k))%nat. 2 : { simpl. lia. }
       replace (S (S k) - 1)%nat with (S ((S k) - 1))%nat. 2 : { simpl. lia. }
    replace (S (S k - 1))%nat with (S k) by lia. unfold Rdiv.
    replace (n * INR (S (S k)) * / (INR (S (S k) * fact (S k)) * m)) with (n * / (INR (fact (S k)) * m)).
    2 : { rewrite mult_INR. field. split. pose proof fact_neq_0 as H3. apply H2. split. apply not_0_INR. apply fact_neq_0. apply not_0_INR. lia. }
    reflexivity.
Qed.

Lemma lemma_2_3_a : forall n k : nat,
  (k >= 1)%nat ->
  choose (S n) k = choose n (k - 1) + choose n k.
Proof.
  intros. assert (H2 : (S n < k \/ S n = k \/ S n > k)%nat) by lia. destruct H2 as [H2 | [H2 | H2]].
  - repeat rewrite k_gt_n_n_choose_k. lra. lia. lia. lia.
  - assert (H3 : (n = k - 1)%nat) by lia. rewrite <- H3. rewrite H2. repeat rewrite n_choose_n.
    rewrite k_gt_n_n_choose_k. lra. lia.
  - unfold choose at 2.
    assert (H3 : (n > k - 1)%nat) by lia. pose proof H3 as H4. apply nltb_gt in H4.
    rewrite H4. unfold choose at 2. assert (H5 : (n >= k)%nat) by lia. pose proof H5 as H6.
    apply nltb_ge in H6. rewrite H6. rewrite fact_div. 2 : { lia. } 2 : { apply not_0_INR. apply fact_neq_0. }
    assert (H7: (n = k)%nat \/ (n > k)%nat) by lia. destruct H7 as [H7 | H7].
    -- rewrite H7. replace ((k - k)%nat) with 0%nat by lia. replace (k - (k - 1))%nat with (1)%nat by lia.
       simpl. repeat rewrite Rmult_1_r. unfold choose. assert (H8 : S k <? k = false). apply nltb_gt. lia.
       rewrite H8. replace (S k - k)%nat with 1%nat by lia. simpl. rewrite Rmult_1_r. rewrite plus_INR.
       rewrite mult_INR. nra.
    -- replace (n - k)%nat with (S (n - k) - 1)%nat by lia. rewrite Rmult_comm with (r2 := INR (fact (S (n - k) - 1))).
       rewrite fact_div with (n := INR (fact n)).
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

Lemma lemma_2_3' : forall n k : nat,
  (k >= 1)%nat -> choose n (S k) = choose (S n) (S k) - choose n k.
Proof.
  intros n k H1. rewrite lemma_2_3_a. 2 : { lia. } replace (S k - 1)%nat with k by lia. lra.
Qed.

Lemma n_choose_1 : forall (n : nat),
  choose n 1 = INR n.
Proof.
  intro n. induction n as [| k IH].
  - compute. lra.
  - rewrite lemma_2_3_a; try lia. rewrite IH. replace (1 - 1)%nat with 0%nat by lia. rewrite n_choose_0. rewrite S_INR. lra.
Qed.

Definition is_natural (r : R) : Prop :=
  exists n : nat, r = INR n.

Lemma is_natural_plus : forall r1 r2 : R,
  is_natural r1 -> is_natural r2 -> is_natural (r1 + r2).
Proof.
  intros r1 r2 H1 H2. destruct H1 as [n1 H1]. destruct H2 as [n2 H2]. exists (n1 + n2)%nat. rewrite H1, H2. rewrite plus_INR. reflexivity.
Qed.

Lemma is_natural_sum_n_nat : forall n : nat,
  (n >= 1)%nat -> is_natural (sum_f 1 n (fun i => INR i)).
Proof.
  intros n H1. induction n as [| k IH]; try lia.
  assert (S k = 1 \/ k >= 1)%nat as [H2 | H2] by lia.
  - rewrite H2. exists 1%nat. compute. reflexivity.
  - rewrite sum_f_i_Sn_f; try lia. apply is_natural_plus; auto. exists (S k). reflexivity.
Qed.

Lemma lemma_2_3_b : forall n k : nat,
  is_natural (choose n k).
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
  (a + b) ^ n = sum_f 0 n (fun i => (choose n i) * a ^ (n - i) * b ^ i).
Proof.
  intros a b n. induction n as [| k IH].
  - compute; lra.
  - replace ((a + b) ^ (S k)) with ((a + b) * (a + b) ^ k) by (simpl; lra).
    rewrite Rmult_plus_distr_r. repeat rewrite IH. repeat rewrite r_mult_sum_f_i_n_f.
    replace (fun i : nat => choose k i * a ^ (k - i) * b ^ i * a) with (fun i : nat => choose k i * a ^ (k - i + 1) * b ^ i).
    2 : { apply functional_extensionality. intros x. replace (choose k x * a ^ (k - x) * b ^ x * a) with (choose k x * (a ^ (k - x) * a) * b ^ x) by lra.
    rewrite pow_equ'. lra. }

    replace (fun i : nat => choose k i * a ^ (k - i) * b ^ i * b) with (fun i : nat => choose k i * a ^ (k - i) * b ^ (i + 1)).
    2 : { apply functional_extensionality. intros x. replace (choose k x * a ^ (k - x) * b ^ x * b) with (choose k x * a ^ (k - x) * (b ^ x * b)) by lra.
    rewrite pow_equ'. lra. } replace (sum_f 0 k (fun i : nat => choose k i * a ^ (k - i) * b ^ (i + 1))) with
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
           rewrite <- Rmult_plus_distr_r with (r3 := a ^ (k - k0 + 1) * b ^ k0). rewrite Rplus_comm. rewrite lemma_2_3_a. 2 : { lia. } lra. }
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
  sum_f 0 n (fun j => choose n j) = 2 ^ n.
Proof.
  intros n. replace 2 with (1 + 1) by lra.
  rewrite lemma_2_3_d. apply sum_f_equiv; try lia.
  intros k H1. repeat rewrite pow1. lra.
Qed.

Lemma lemma_2_3_e_ii : forall n, 
  (n >= 1)%nat ->
    sum_f 0 n (fun j => (-1) ^ j * choose n j) = 0.
Proof.
  intros n H1. replace 0 with ((1 + -1)^n). 2 : { replace (1 + -1) with 0 by lra. rewrite Rpow_0; auto. }
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
  (n >= 1)%nat -> sum_f 0 n (fun l => if Nat.odd l then choose n l else 0) = 2 ^ (n - 1).
Proof.
  intros n H1. assert (H2 : 2 * sum_f 0 n (fun l => if Nat.odd l then choose n l else 0) = sum_f 0 n (fun j => choose n j) - sum_f 0 n (fun j => (-1) ^ j * choose n j)).
  - rewrite sum_f_minus; try lia. rewrite r_mult_sum_f_i_n_f. apply sum_f_equiv; try lia. intros k H2. destruct (Nat.odd k) eqn:H3.
    -- rewrite Nat.odd_spec in H3. destruct H3 as [m H3]. replace (2 * m + 1)%nat with (S (2 * m)) in H3 by lia. rewrite H3 at 3. rewrite pow_1_odd. lra.
    -- pose proof Nat.orb_even_odd n as H4. assert (H5 : Nat.even k = true) by (apply odd_spec_false; auto). rewrite Nat.even_spec in H5. destruct H5 as [m H5]. rewrite H5. rewrite pow_1_even. lra.
  - apply Rmult_eq_compat_l with (r := / 2) in H2. rewrite <- Rmult_assoc in H2. rewrite Rinv_l in H2; try lra. rewrite Rmult_1_l in H2. rewrite H2. rewrite lemma_2_3_e_i. rewrite lemma_2_3_e_ii; try lia.
    rewrite Rminus_0_r. replace n%nat with (S (n-1))%nat at 1 by lia. simpl. lra.
Qed.

Lemma lemma_2_3_e_iv : forall n,
  (n >= 1)%nat -> sum_f 0 n (fun l => if Nat.even l then choose n l else 0) = 2 ^ (n - 1).
Proof.
  intros n H1. assert (H2 : 2 * sum_f 0 n (fun l => if Nat.even l then choose n l else 0) = sum_f 0 n (fun j => choose n j) + sum_f 0 n (fun j => (-1) ^ j * choose n j)).
  - rewrite sum_f_plus; try lia. rewrite r_mult_sum_f_i_n_f. apply sum_f_equiv; try lia. intros k H2. destruct (Nat.even k) eqn:H3.
    -- rewrite Nat.even_spec in H3. destruct H3 as [m H3]. rewrite H3. rewrite pow_1_even. lra.
    -- pose proof Nat.orb_even_odd n as H4. assert (H5 : Nat.odd k = true) by (apply even_spec_false; auto). rewrite Nat.odd_spec in H5. destruct H5 as [m H5].
       replace (2 * m + 1)%nat with (S (2 * m)) in H5 by lia. rewrite H5 at 2. rewrite pow_1_odd. lra. 
  - apply Rmult_eq_compat_l with (r := / 2) in H2. rewrite <- Rmult_assoc in H2. rewrite Rinv_l in H2; try lra. rewrite Rmult_1_l in H2. rewrite H2. rewrite lemma_2_3_e_i. rewrite lemma_2_3_e_ii; try lia.
    rewrite Rplus_0_r. replace n%nat with (S (n-1))%nat at 1 by lia. simpl. lra.
Qed.

Lemma sum_f_l_n_0 : forall l n, (l <= n)%nat ->
  sum_f l n (fun i => 0) = 0.
Proof.
  intros l n H1. induction n as [| k IH].
  - destruct l. repeat rewrite sum_f_0_0. reflexivity. rewrite sum_f_Sn_n; try lia; try lra.
  - assert (l = S k \/ l <= k)%nat as [H2 | H2] by lia.
    -- rewrite <- H2. rewrite sum_f_n_n. reflexivity.
    -- rewrite sum_f_i_Sn_f; try lia. rewrite IH; try lia. lra.
Qed.

Lemma lemma_2_4_a : forall l m n,
  sum_f 0 l (fun i => choose n i * choose m (l - i)) = choose (n + m) l.
Proof.
  intros l m n.  generalize dependent l. induction m as [| m' IHn].
  - induction n as [| n' IHm].
    -- intros l. destruct l.
      --- repeat rewrite sum_f_0_0. repeat rewrite n_choose_0. lra.
      --- rewrite sum_f_i_Sn_f; try lia. rewrite O_choose_n; try lia. rewrite Rmult_0_l. rewrite Rplus_0_r. rewrite O_choose_n; try lia.
          replace (fun i : nat => choose 0 i * choose 0 (S l - i)) with (fun i : nat => 0).
          { rewrite sum_f_l_n_0; try lia. reflexivity. } apply functional_extensionality. intros x. assert (x = 0 \/ x <> 0)%nat as [H1 | H1] by lia.
          rewrite H1. rewrite n_choose_0. rewrite O_choose_n. lra. lia. rewrite O_choose_n. lra. auto.
    -- intros l. destruct l.
      --- rewrite sum_f_0_0. repeat rewrite n_choose_0. lra.
      --- rewrite sum_f_i_Sn_f; try lia. replace (S l - S l)%nat with 0%nat by lia. rewrite n_choose_0.
          replace (sum_f 0 l (fun i : nat => choose (S n') i * choose 0 (S l - i))) with (sum_f 0 l (fun _ => 0)).
          2 : { apply sum_f_congruence; try lia. intros x H1. rewrite O_choose_n; try lia. lra. }
          rewrite sum_f_l_n_0; try lia. rewrite Nat.add_0_r. lra.
  - intros l. replace (n + S m')%nat with (S (n + m')) by lia. assert (l = 0 \/ l >= 1)%nat as [H1 | H1] by lia.
    -- rewrite H1. rewrite sum_f_0_0. repeat rewrite n_choose_0. lra.
    -- rewrite lemma_2_3_a; try lia. pose proof IHn as H2. pose proof IHn as H3.
       specialize (H2 l). specialize (H3 (l - 1)%nat). rewrite <- H2. rewrite <- H3.
       replace (sum_f 0 l (fun i : nat => choose n i * choose m' (l - i))) with (choose n l + sum_f 0 (l -1) (fun i : nat => choose n i * choose m' (l - i))).
       2 : { replace (l) with (S (l - 1)) by lia. rewrite sum_f_i_Sn_f; try lia. replace (S (l - 1) - (S (l - 1)))%nat with 0%nat by lia. 
             rewrite n_choose_0. rewrite Rmult_1_r. replace (S (l - 1))%nat with l by lia. lra. }
       rewrite Rplus_comm. rewrite Rplus_assoc. rewrite sum_f_sum.
       replace (fun x : nat => choose n x * choose m' (l - x) + choose n x * choose m' (l - 1 - x)) with (fun x : nat => choose n x * (choose m' (l-x) + choose m' (l - 1- x))).
       2 : { apply functional_extensionality. intros x. lra. }
       replace (sum_f 0 (l - 1) (fun x : nat => choose n x * (choose m' (l - x) + choose m' (l - 1 - x)))) with (sum_f 0 (l-1) (fun x : nat => choose n x * choose (S m') (l - x))).
       2 : { apply sum_f_equiv. lia. intros x H4. rewrite Rplus_comm. replace (l - 1 - x)%nat with ((l-x) -1)%nat by lia. rewrite <- lemma_2_3_a. lra. lia. }
       replace (choose n l) with (choose n l * choose (S m') 0) by (rewrite n_choose_0; lra). rewrite Rplus_comm. replace (l - 1)%nat with (Nat.pred l) by lia.
       set (f := fun x : nat => choose n x * choose (S m') (l - x)). replace (choose n l * choose (S m') 0) with (f l).
       2 : { unfold f. replace (l - l)%nat with 0%nat by lia. lra. } rewrite <- sum_f_Pn; try lia. unfold f. apply sum_f_equiv. lia. intros x H5.
       assert (l - x = 0 \/ l - x >= 1)%nat as [H6 | H6] by lia.
       --- rewrite H6. repeat rewrite n_choose_0. repeat rewrite Rmult_1_r. lra.
       --- lra.
Qed.

Lemma n_choose_k_equiv : forall n k : nat,
  (k <= n)%nat -> choose n k = choose n (n - k).
Proof.
  intros n. induction n as [| n' IH].
  - destruct k; try lia. simpl. reflexivity.
  - intros k H1. assert (k = S n' \/ k <= n')%nat as [H2 | H2] by lia.
    -- rewrite H2. rewrite n_choose_n. replace (S n' - S n')%nat with 0%nat by lia. rewrite n_choose_0. reflexivity.
    -- assert (k = 0 \/ k >= 1)%nat as [H3 | H3] by lia.
       --- rewrite H3. rewrite n_choose_0. replace (S n' - 0)%nat with (S n')%nat by lia. rewrite n_choose_n. reflexivity.
       --- repeat rewrite lemma_2_3_a; try lia. replace (S n' - k - 1)%nat with (n' - k)%nat by lia. rewrite IH with (k := k); try lia.
           replace (S n' - k)%nat with (n' - (k - 1))%nat by lia. rewrite <- IH with (k := (k-1)%nat); try lia. lra.
Qed.

Lemma lemma_2_4_b : forall n : nat,
  sum_f 0 n (fun k : nat => (choose n k) ^ 2) = choose (2 * n)%nat n.
Proof.
  intros n. replace (2 * n)%nat with (n + n)%nat by lia. rewrite <- lemma_2_4_a with (m := n) (n := n).
  apply sum_f_equiv; try lia. intros k H1. rewrite n_choose_k_equiv; try lia. lra.
Qed.

Lemma lemma_2_5_a : forall n r,
  r <> 1 -> sum_f 0 n (fun i => r ^ i) = (1 - r ^ (n+1)) / (1 - r).
Proof.
  intros n r H1. induction n as [| k IH].
  - compute. field. nra.
  - destruct k as [| k'] eqn : Ek.
    -- compute. field. nra.
    -- rewrite sum_f_i_Sn_f. 2 : { lia. }
       rewrite IH. rewrite <- Ek. apply Rmult_eq_reg_l with (r := (1 - r)).
       2 : { nra. }
       replace ((1 - r) * ((1 - r ^ (k + 1)) / (1 - r) + r ^ S k)) with (1 - r^(k+1) + r^S k - r * r^S k) by (field; nra).
       replace ((1 - r) * ((1 - r ^ (S k + 1)) / (1 - r))) with (1 - r^(S k + 1)) by (field; nra).
       replace (r^(S k + 1)) with (r * r ^ (S k)). 2 : { replace (S k + 1)%nat with (S (S k)) by lia. simpl. auto. }
       simpl. apply Rplus_eq_reg_r with (r := r * (r * r^k)).
       replace (1 - r ^ (k + 1) + r * r ^ k - r * (r * r ^ k) + r * (r * r ^ k)) with
               (1 - r ^(k+1) + r * r^k) by nra.
       replace (1 - r * (r * r ^ k) + r * (r * r ^ k)) with 1 by nra.
       replace (k+1)%nat with (S k) by lia. simpl. lra.
Qed.

Lemma lemma_2_5_b : forall n r,
  r <> 1 -> sum_f 0 n (fun i => r ^ i) = (1 - r ^ (n+1)) / (1 - r).
Proof.
  intros n r H1. set (Sum := sum_f 0 n (fun i => r ^ i)).
  assert (H2 : r * Sum = sum_f 0 n (fun i => r ^ (S i))).
  { unfold Sum. rewrite r_mult_sum_f_i_n_f. apply sum_f_equiv. lia. intros k H2. simpl. lra. }
  assert (r = 0 \/ r <> 0) as [H3 | H3] by lra; assert (n = 0 \/ n > 0)%nat as [H4 | H4] by lia.
  - unfold Sum. rewrite H4. rewrite H3. rewrite sum_f_0_0. simpl. field.
  - unfold Sum. rewrite H3 in *. rewrite sum_f_Si; try lia. 
    replace (sum_f 1 n (fun i => 0 ^ i)) with (sum_f 1 n (fun i => 0)).
    2 : { apply sum_f_equiv. lia. intros k H5. destruct k. lia. simpl. lra. }
    rewrite sum_f_const. simpl. replace (n+1)%nat with (S n) by lia. simpl. lra.
  - unfold Sum. rewrite H4 in *. rewrite sum_f_0_0. simpl. field; lra.
  -  assert (H5 : r * Sum = sum_f 1 (n+1) (fun i : nat => r^i)).
    { rewrite sum_f_reindex with (s := 1%nat); try lia. simpl. replace (n + 1 - 1)%nat with n%nat by lia.
      replace (fun x : nat => r ^ (x + 1)) with (fun x : nat => r ^ (S x)). 
      2 : { apply functional_extensionality. intros x. replace (x + 1)%nat with (S x) by lia. reflexivity. }
      rewrite H2. apply sum_f_equiv; try lia. intros k H5. reflexivity.
    } assert (H6 : Sum - r * Sum = 1 - r^(n + 1)).
    { rewrite H5. unfold Sum. rewrite sum_f_Si_n_f with (i := 0%nat); try lia. replace (n+1)%nat with (S n) by lia.
      rewrite sum_f_i_Sn_f with (n := n); try lia. lra. }
    assert (H7 : Sum * (1 - r) = 1 - r ^ (n+1)) by nra. apply Rmult_eq_compat_r with (r := 1 / (1 - r)) in H7.
    field_simplify in H7; try nra. rewrite H7. field; nra.
Qed.

Lemma sum_f_1_n_fSi_minus_fi : forall n (f : nat -> R),
  (n >= 1)%nat -> sum_f 1 n (fun i => f (i+1)%nat - f i) = f (n+1)%nat - f 1%nat.
Proof.
  intros n f H1. induction n as [| n' IH]; try lia.
  assert (S n' = 1 \/ n' >= 1)%nat as [H2 | H2] by lia.
  - rewrite H2. compute. reflexivity.
  - rewrite sum_f_i_Sn_f; try lia. rewrite IH; try lia. 
    replace (S n') with (n' + 1)%nat by lia. lra.
Qed.

Lemma sum_f_1_n_fi_minus_fSi : forall n (f : nat -> R),
  (n >= 1)%nat -> sum_f 1 n (fun i => f i - f (i+1)%nat) = f 1%nat - f (n+1)%nat.
Proof.
  intros n f H1. induction n as [| n' IH]; try lia.
  assert (S n' = 1 \/ n' >= 1)%nat as [H2 | H2] by lia.
  - rewrite H2. compute. reflexivity.
  - rewrite sum_f_i_Sn_f; try lia. rewrite IH; try lia. 
    replace (S n') with (n' + 1)%nat by lia. lra.
Qed.

Lemma lemma_2_6_i : forall n,
  (n >= 1)%nat -> sum_f 1 n (fun i => INR i ^ 3) = INR n^4 / 4 + INR n^3 / 2 + INR n^2 / 4.
Proof.
  intros n H1. 
  assert (H2 : forall r, (r + 1)^4 - r^4 = 4 * r^3 + 6 * r^2 + 4 * r + 1) by (intros; nra).
  assert (H3 : sum_f 1 n (fun k : nat => INR (k + 1) ^ 4 - INR k ^ 4) = INR (n+1)^4 - 1).
  {
    set (f := fun x => INR x ^ 4). replace (INR (n + 1)^4) with (f (n+1)%nat) by reflexivity. replace 1 with (f 1%nat) by (compute; lra).
    apply sum_f_1_n_fSi_minus_fi with (n := n) (f := fun x => INR x ^ 4); lia.
  }
  assert (H4 : sum_f 1 n (fun k => 4 * INR k ^ 3 + 6 * INR k ^ 2 + 4 * INR k + 1) = 4 * sum_f 1 n (fun k => INR k^3) + 6 * sum_f 1 n (fun k => INR k^2) + 4 * sum_f 1 n (fun k => INR k) + INR n).
  {
    clear H3.
    induction n as [| n' IH]; try lia. assert (S n' = 1 \/ n' >= 1)%nat as [H3 | H3] by lia.
    - rewrite H3. compute. nra.
    - repeat rewrite sum_f_i_Sn_f; try lia. rewrite IH; auto. repeat rewrite S_INR. simpl. nra.
  }
  replace (sum_f 1 n (fun k : nat => INR k)) with (INR n * (INR n + 1) / 2) in H4 by (rewrite sum_n_nat; auto).
  replace (sum_f 1 n (fun k : nat => INR k ^ 2)) with (INR n * (INR n + 1) * (2 * INR n + 1) / 6) in H4 by (rewrite lemma_2_1_i; auto).
  assert (H5 : (fun k : nat => INR (k + 1) ^ 4 - INR k ^ 4) = (fun k : nat => 4 * INR k ^ 3 + 6 * INR k ^ 2 + 4 * INR k + 1)).
  { apply functional_extensionality. intros x. specialize (H2 (INR x)). rewrite plus_INR. replace (INR 1) with 1 by reflexivity. apply H2. }
  rewrite <- H5 in H4. rewrite H3 in H4. replace (sum_f 1 n (fun i : nat => INR i ^ 3)) with 
  ((INR (n + 1) ^ 4 - 1 - 6 * (INR n * (INR n + 1) * (2 * INR n + 1) / 6) - 4 * (INR n * (INR n + 1) / 2) - INR n) / 4) by nra.
  rewrite plus_INR. simpl. nra.
Qed.

Lemma lemma_2_6_ii : forall n,
  (n >= 1)%nat -> sum_f 1 n (fun i => INR i ^ 4) = INR n^5 / 5 + INR n^4 / 2 + INR n^3 / 3 - INR n / 30.
Proof.
  intros n H1.
  assert (H2 : forall r, (r + 1)^5 - r^5 = 5 * r^4 + 10 * r^3 + 10 * r^2 + 5 * r + 1) by (intros; nra).
  assert (H3 : sum_f 1 n (fun k : nat => INR (k + 1) ^ 5 - INR k ^ 5) = INR (n+1)^5 - 1).
  { 
    set (f := fun x => INR x ^ 5). replace (INR (n + 1)^5) with (f (n+1)%nat) by reflexivity. replace 1 with (f 1%nat) by (compute; lra).
    apply sum_f_1_n_fSi_minus_fi with (n := n) (f := fun x => INR x ^ 5); lia.
  }
  assert (H4 : sum_f 1 n (fun k => 5 * INR k ^ 4 + 10 * INR k ^ 3 + 10 * INR k ^ 2 + 5 * INR k + 1) = 5 * sum_f 1 n (fun k => INR k^4) + 10 * sum_f 1 n (fun k => INR k^3) + 10 * sum_f 1 n (fun k => INR k^2) + 5 * sum_f 1 n (fun k => INR k) + INR n).
  {
    clear H3.
    induction n as [| n' IH]; try lia. assert (S n' = 1 \/ n' >= 1)%nat as [H3 | H3] by lia.
    - rewrite H3. compute. nra.
    - repeat rewrite sum_f_i_Sn_f; try lia. rewrite IH; auto. repeat rewrite S_INR. simpl. nra.
  }
  replace (sum_f 1 n (fun k : nat => INR k)) with (INR n * (INR n + 1) / 2) in H4 by (rewrite sum_n_nat; auto).
  replace (sum_f 1 n (fun k : nat => INR k ^ 2)) with (INR n * (INR n + 1) * (2 * INR n + 1) / 6) in H4 by (rewrite lemma_2_1_i; auto).
  replace (sum_f 1 n (fun k : nat => INR k ^ 3)) with (INR n^4 / 4 + INR n^3 / 2 + INR n^2 / 4) in H4 by (rewrite lemma_2_6_i; auto).
  assert (H5 : (fun k : nat => INR (k + 1) ^ 5 - INR k ^ 5) = (fun k : nat => 5 * INR k ^ 4 + 10 * INR k ^ 3 + 10 * INR k ^ 2 + 5 * INR k + 1)).
  { apply functional_extensionality. intros x. specialize (H2 (INR x)). rewrite plus_INR. replace (INR 1) with 1 by reflexivity. apply H2. }
  rewrite <- H5 in H4. rewrite H3 in H4. replace (sum_f 1 n (fun i : nat => INR i ^ 4)) with 
  ((INR (n + 1) ^ 5 - 1 - 10 * (INR n ^ 4 / 4 + INR n ^ 3 / 2 + INR n ^ 2 / 4) - (10 * (INR n * (INR n + 1) * (2 * INR n + 1) / 6)) - 5 * (INR n * (INR n + 1) / 2) - INR n) / 5) by nra.
  rewrite plus_INR. simpl. nra.
Qed.

Lemma lemma_2_6_iii : forall n,
  (n >= 1)%nat -> sum_f 1 n (fun i => 1 / INR (i * (i + 1))) = 1 - 1 / INR (n + 1).
Proof.
  intros n H1.
  set (f := fun x => 1 / INR x). replace 1 with (f 1%nat) at 1 by (compute; lra).
  replace (1 / INR (n + 1)) with (f (n + 1)%nat) at 1 by reflexivity. rewrite <- sum_f_1_n_fi_minus_fSi with (n := n) (f := f); try lia.
  apply sum_f_equiv; try lia. intros k H2. unfold f. rewrite mult_INR. repeat rewrite plus_INR. simpl. field. split.
  - rewrite <- INR_1. rewrite <- plus_INR. apply not_0_INR. lia.
  - apply not_0_INR. lia.
Qed.

Lemma lemma_2_6_iv : forall n,
  (n >= 1)%nat -> sum_f 1 n (fun i => INR (2 * i + 1) / INR (i^2 * (i + 1)^2)) = 1 - 1 / (INR (n + 1)^2).
Proof.
  intros n H1.
  set (f := fun x => 1 / INR (x^2)). replace 1 with (f 1%nat) at 1 by (compute; lra).
  replace (1 / INR (n + 1)^2) with (f (n + 1)%nat). 2 : { unfold f. rewrite pow_INR. reflexivity. } 
  rewrite <- sum_f_1_n_fi_minus_fSi with (n := n) (f := f); try lia. apply sum_f_equiv; try lia. intros k H2.
  unfold f. simpl. repeat rewrite mult_INR. repeat rewrite plus_INR. simpl. field. split.
  - rewrite <- INR_1. rewrite <- plus_INR. apply not_0_INR. lia.
  - apply not_0_INR. lia.
Qed.

Open Scope nat_scope. 

Lemma lemma_2_8 : forall n : nat,
  Nat.Even n \/ Nat.Odd n.
Proof.
  intros n. induction n as [| k IH].
  - left. unfold Nat.Even. exists 0. lia.
  - destruct IH as [IH | IH].
    -- right. unfold Nat.Odd in *. destruct IH as [k0 H]. exists (k0). lia.
    -- left. unfold Nat.Even in *. destruct IH as [k0 H]. exists (S k0). lia.
Qed.

Lemma lemma_2_8' : forall z : Z,
  Z.Even z \/ Z.Odd z.
Proof.
  intros z. rewrite <- Zeven_equiv. rewrite <- Zodd_equiv.
  destruct (Zeven_odd_dec z) as [H | H].
  - auto.
  - auto.
Qed.

Lemma lemma_2_9 : forall (A : nat -> Prop) (n0 : nat),
  (A n0 /\ (forall k : nat, A k -> A (S k))) ->
  forall n : nat, n >= n0 -> A n.
Proof.
  intros A n0 [H1 H2] n H3.
  induction n as [| k IH].
  - inversion H3. rewrite H in H1. apply H1.
  - assert (H4 : n0 = S k \/ n0 < S k) by lia. destruct H4 as [H4 | H4].
    -- rewrite H4 in H1. apply H1.
    -- apply H2. apply IH. lia.
Qed.

Definition induction_nat := forall P : nat -> Prop,
  (P 0 /\ (forall k : nat, P k -> P (S k))) -> forall n, P n.

Definition strong_induction_nat := forall P : nat -> Prop,
  (forall m, (forall k : nat, k < m -> P k) -> P m) -> forall n, P n.

Definition well_ordering_nat := forall E : nat -> Prop,
  (exists x, E x) -> (exists n, E n /\ forall m, E m -> (n <= m)).

Definition well_ordering_principle_contrapositive_nat := forall E : nat -> Prop,
  (~(exists m, E m /\ forall k, E k -> m <= k)) -> (~(exists n, E n)).

Lemma induction_imp_induction_nat : induction_nat.
Proof.
  unfold induction_nat. intros P [H_base H_ind] n.
  induction n as [| k IH].
  - apply H_base.
  - apply H_ind. apply IH.
Qed.

Lemma lemma_2_10 : well_ordering_nat -> induction_nat.
Proof.
  unfold well_ordering_nat, induction_nat. intros well_ordering_nat P [Hbase H_inductive] n.
  set (E := fun m => ~ P m).
  specialize (well_ordering_nat E). assert (H1 : forall n : nat, E n -> False).
  - intros x H1. assert (H3 : exists x, E x) by (exists x; auto). apply well_ordering_nat in H3.
    destruct H3 as [least_elem_E H3]. destruct H3 as [H3 H4]. specialize (H_inductive (least_elem_E - 1)).
    destruct least_elem_E as [| least_elem_E'].
    -- apply H3. apply Hbase.
    -- specialize (H4 least_elem_E'). assert (H5 : S least_elem_E' <= least_elem_E' -> False) by lia.
       assert (H6 : ~(E least_elem_E')) by tauto. unfold E in H6. simpl in *. rewrite Nat.sub_0_r in *.
       apply NNPP in H6. apply H_inductive in H6. apply H3. apply H6.
  - specialize (H1 n). unfold E in H1. apply NNPP in H1. apply H1.
Qed.

Lemma lemma_2_11 : induction_nat -> strong_induction_nat.
Proof.
  unfold induction_nat, strong_induction_nat. intros induction_nat P H1 n.
  assert (H2 : forall k, k <= n -> P k).
  - apply induction_nat with (n := n). split.
    -- intros k Hk. inversion Hk. apply H1. intros k' Hk'. inversion Hk'.
    -- intros k Hk. intros k' Hk'. apply H1. intros k'' Hk''. apply Hk. lia.
  - apply H2. lia.
Qed.

Lemma strong_induction_nat_imp_well_ordering_contrapositive_nat : strong_induction_nat -> well_ordering_principle_contrapositive_nat.
Proof.
  intros H1 E H2. set (E' := fun n => ~ E n). assert (~ E 0) as H3.
  { intros H3. apply H2. exists 0. split; auto; lia. }
  assert (H4 : forall n, E' n).
  {
    intros n. apply H1. intros m H4. destruct m.
    - unfold E'. intros H5. apply H3. apply H5.
    - assert (E (S m) -> False) as H5.
      { 
        intros H5. apply H2. exists (S m). split; auto. intros k H6.
        specialize (H4 k). assert (E' k -> False) as H7; auto. assert (k < S m -> False) as H8 by auto. lia.
      }
      auto.
  }
  intros [n H5]. apply (H4 n). auto.
Qed.

Lemma strong_induction_nat_imp_well_ordering_nat : strong_induction_nat -> well_ordering_nat.
Proof.
  intros H1. specialize (strong_induction_nat_imp_well_ordering_contrapositive_nat H1) as H2.
  clear H1. rename H2 into H1. intros E H2. 
  assert (H3 : ~(exists m, E m /\ forall k, E k -> m <= k) -> ~(exists n, E n)) by apply H1.
  destruct (classic (exists m, E m /\ forall k, E k -> m <= k)) as [H4 | H4]; auto.
  exfalso. apply H3 in H4. apply H4. apply H2.
Qed.

Lemma WI_SO_WO_equiv : (well_ordering_nat <-> strong_induction_nat) /\ (strong_induction_nat <-> induction_nat) /\ (induction_nat <-> well_ordering_nat).
Proof.
  pose proof lemma_2_10 as H1. pose proof lemma_2_11 as H2. pose proof (strong_induction_nat_imp_well_ordering_nat) as H3. tauto.
Qed.

Lemma WI_SO_WO : well_ordering_nat /\ strong_induction_nat /\ induction_nat.
Proof.
  pose proof WI_SO_WO_equiv as H1. pose proof (induction_imp_induction_nat) as H2. tauto.
Qed. 

Lemma strong_induction_N : strong_induction_nat.
Proof.
  apply lemma_2_11. apply induction_imp_induction_nat.
Qed.

Ltac strong_induction n :=
  apply (strong_induction_N (fun n => _));
  let n := fresh n in
  intros n IH.

Open Scope R_scope.

Definition rational (r : R) : Prop :=
  exists z1 z2 : Z, (r = (IZR z1) / (IZR z2))%R.

Definition irrational (r : R) : Prop :=
  ~ rational r.

Lemma choose_rational : forall (m n : nat),
  rational (choose m n).
Proof.
  intros m n. pose proof (lemma_2_3_b m n) as [q H1]. rewrite H1. exists (Z.of_nat q), (1%Z). field_simplify. apply INR_IZR_INZ.
Qed.

Lemma exist_R_plus_eq_l : forall (r r1 : R) (f : list R -> R) (s : nat),
  (exists l, length l = s /\ Forall (fun r : R => rational r) l /\ r1 = (f l)) -> (exists l, length l = s /\ Forall (fun r : R => rational r) l /\ r + r1 = r + f l).
Proof.
  intros. destruct H as [l H]. exists l. repeat split; try tauto. lra.
Qed.

Fixpoint build_list_for_lemma_2_7 (m i : nat) : list R :=
  match i with
  | 0 => []
  | S i' => build_list_for_lemma_2_7 m i' ++ [choose (m + 1) i]
  end.

Lemma build_list_for_lemma_2_7_length : forall m i,
  length (build_list_for_lemma_2_7 m i) = i.
Proof.
  intros. induction i as [| i' IH].
  - reflexivity.
  - simpl. rewrite app_length. rewrite IH. simpl. lia.
Qed.

Lemma build_list_for_lemma_2_7_rational : forall m i,
  Forall (fun r : R => rational r) (build_list_for_lemma_2_7 m i).
Proof.
  intros. induction i as [| i' IH].
  - apply Forall_nil.
  - simpl. apply Forall_app. split.
    + apply IH.
    + apply Forall_cons. apply choose_rational. apply Forall_nil.
Qed.

Lemma build_list_for_lemma_2_7_sum : forall m n i,
  (m >= 2)%nat -> (i >= 2)%nat -> sum_f 1 i (fun j : nat => choose (m + 1) j * INR n ^ j) = sum_f 0 (i - 1) (fun j : nat => nth j (build_list_for_lemma_2_7 m i) 0 * INR n ^ (j + 1)).
Proof.
  intros. induction i as [| i' IH].
  - lia.
  - assert (S i' = 2 \/ i' >= 2)%nat as [H1 | H1] by lia.
    -- rewrite H1. compute; lra.
    -- apply IH in H1. rewrite sum_f_i_Sn_f; try lia. rewrite H1. replace (S i' - 1)%nat with (S (i' -1)) by lia. rewrite sum_f_i_Sn_f; try lia. 
       replace (nth (S (i' - 1)) (build_list_for_lemma_2_7 m (S i')) 0) with (choose (m + 1) (S i')).
       2 : { simpl. rewrite app_nth2; try lia. 2 : { rewrite build_list_for_lemma_2_7_length. lia. } rewrite build_list_for_lemma_2_7_length. replace (S (i' - 1) - i')%nat with 0%nat by lia. reflexivity. }
       replace (S (i' - 1) + 1)%nat with (S i') by lia. replace (sum_f 0 (i' - 1) (fun j : nat => nth j (build_list_for_lemma_2_7 m (S i')) 0 * INR n ^ (j + 1))) with (sum_f 0 (i' - 1) (fun j : nat => nth j (build_list_for_lemma_2_7 m i') 0 * INR n ^ (j + 1))).
       2 : { apply sum_f_equiv; try lia. intros k H2. simpl. rewrite app_nth1. reflexivity. rewrite build_list_for_lemma_2_7_length. lia. } lra.
Qed.

Lemma test_lemma1 : forall (a c : nat) (f : nat -> list R -> Prop),
  (a <= c)%nat -> (forall b : nat, (a <= b <= c)%nat -> exists l1 : list R, f b l1) -> exists l2 : list (list R), (length l2 = c - a + 1)%nat /\ Forall (fun l1 : list R => (forall i : nat, ((0 <= i < length l2)%nat /\ nth i l2 [] = l1) -> f (a + i)%nat l1)) l2.
Proof.
  intros a c f H1 H2. induction c as [| c' IH].
  - replace a with 0%nat by lia. specialize (H2 0%nat). assert (H3 : (a <= 0 <= 0)%nat) by lia. apply H2 in H3. destruct H3 as [l1 H3]. exists [l1]. split.
    + simpl. lia.
    + apply Forall_cons. intros i H4. destruct H4 as [H4 H5]. simpl in H4. assert (i = 0)%nat by lia. rewrite H. apply H3.
      rewrite Forall_forall. intros x H6 i [H7 H8]. inversion H6. 
  - assert (a = S c' \/ a <= c')%nat as [H3 | H3] by lia.
    -- rewrite H3. assert (H4 : (a <= a <= S c')%nat) by lia. apply H2 in H4. destruct H4 as [l1 H4]. exists [l1]. split. simpl. lia. apply Forall_cons.
       intros i H5. destruct H5 as [H5 H6]. simpl in H5. assert (i = 0)%nat by lia. rewrite H. rewrite <- H3. simpl. rewrite Nat.add_0_r. apply H4. rewrite Forall_forall. intros x H7 i [H8 H9]. inversion H7.
    -- specialize (IH H3). assert (H4 : forall b : nat, (a <= b <= c')%nat -> exists l1 : list R, f b l1).
       { intros b H4. assert (H5 : (a <= b <= S c')%nat) by lia. apply H2 in H5. destruct H5 as [l1 H5]. exists l1. auto. }
       specialize (IH H4). destruct IH as [l2 [H5 H6]]. rewrite Forall_forall in H6. pose proof H2 as H2'. specialize (H2 (S c')). assert (H7 : (a <= S c' <= S c')%nat) by lia. apply H2 in H7. destruct H7 as [l1 H7]. exists (l2 ++ [l1]). split.
       + rewrite app_length. rewrite H5. replace (length [l1]) with 1%nat by reflexivity. lia.
       + apply Forall_app. split.
         * rewrite Forall_forall. intros x H8 i [H9 H10]. assert (H11 : (length (l2 ++ [l1]) = S (c' - a + 1))%nat). { rewrite app_length. rewrite H5. replace (length [l1]) with 1%nat by reflexivity. lia. }
           assert (i = length l2 \/ i < length l2)%nat as [H12 | H12]. { lia. }
           ++ rewrite H5 in H12. rewrite H12. replace (a + (c' - a + 1))%nat with (S c') by lia. rewrite app_nth2 in H10; try lia. rewrite H12 in H10. rewrite H5 in H10. replace (c' - a + 1 - (c' - a + 1))%nat with 0%nat in H10 by lia.
              simpl in H10. rewrite <- H10. auto.
           ++ apply H6; auto. split. lia. rewrite app_nth1 in H10; try lia. apply H10.
         * rewrite Forall_forall. intros x H8 i [H9 H10]. simpl in H8. destruct H8 as [H8 | H8]; try tauto. rewrite <- H8. rewrite app_length in H9. rewrite H5 in H9. simpl in H9.
           assert (i = (c' - a + 1) \/ i < (c' - a + 1))%nat as [H11 | H11] by lia.
           ++ rewrite H11. replace (a + (c' - a + 1))%nat with (S c') by lia. auto.
           ++ specialize (H6 x). rewrite app_nth1 in H10; try lia. assert (In x l2) as H12. { rewrite <- H5 in H11. apply nth_In with (d := []) in H11. rewrite H10 in H11. auto. }
              specialize (H6 H12). rewrite H8. apply H6. split. lia. apply H10.
Qed.

Lemma test_lemma2 : forall (a c n : nat) (f : nat -> list R -> Prop),
  (a <= c)%nat -> (forall b : nat, (a <= b <= c)%nat -> exists l1 : list R, (length l1 = n /\ Forall rational l1 /\ f b l1)) -> exists l2 : list (list R), (length l2 = c - a + 1)%nat /\ Forall (fun l1 : list R => length l1 = n /\ Forall rational l1 /\ (forall i : nat, ((0 <= i < length l2)%nat /\ nth i l2 [] = l1) -> f (a + i)%nat l1)) l2.
Proof.
  intros a c n f H1 H2. induction c as [| c' IH].
  - replace a with 0%nat by lia. specialize (H2 0%nat). assert (H3 : (a <= 0 <= 0)%nat) by lia. apply H2 in H3. destruct H3 as [l1 [H3 H4]]. exists [l1]. split.
    -- simpl. lia.
    -- apply Forall_cons. repeat split;try tauto. intros i H5. destruct H5 as [H5 H6]. simpl in H5. assert (i = 0)%nat by lia. rewrite H. apply H4.
       rewrite Forall_forall. intros x H7. inversion H7.
  - assert (a = S c' \/ a <= c')%nat as [H3 | H3] by lia.
    -- rewrite H3. assert (H4 : (a <= a <= S c')%nat) by lia. apply H2 in H4. destruct H4 as [l1 [H4 H5]]. exists [l1]. split. simpl. lia. apply Forall_cons. repeat split;try tauto.
       intros i H6. destruct H6 as [H6 H7]. simpl in H6. assert (i = 0)%nat by lia. rewrite H. rewrite <- H3. simpl. rewrite Nat.add_0_r. apply H5.
       rewrite Forall_forall. intros x H8. inversion H8.
    -- specialize (IH H3). assert (H4 : forall b : nat, (a <= b <= c')%nat -> exists l1 : list R, (length l1 = n /\ Forall rational l1 /\ f b l1)).
       { intros b H4. assert (H5 : (a <= b <= S c')%nat) by lia. apply H2 in H5. destruct H5 as [l1 [H5 H6]]. exists l1. tauto. }
       specialize (IH H4). destruct IH as [l2 [H5 H6]]. rewrite Forall_forall in H6. pose proof H2 as H2'. specialize (H2 (S c')). assert (H7 : (a <= S c' <= S c')%nat) by lia. apply H2 in H7. destruct H7 as [l1 [H7 H8]]. exists (l2 ++ [l1]). split.
       + rewrite app_length. rewrite H5. replace (length [l1]) with 1%nat by reflexivity. lia.
       + apply Forall_app. repeat split; try tauto.
         * rewrite Forall_forall. intros x H9. repeat split; try tauto.
           ++ specialize (H6 x). tauto.
           ++ specialize (H6 x). tauto.
           ++ intros i [H10 H11]. assert (H12 : (length (l2 ++ [l1]) = S (c' - a + 1))%nat). { rewrite app_length. rewrite H5. replace (length [l1]) with 1%nat by reflexivity. lia. }
              assert (i = length l2 \/ i < length l2)%nat as [H13 | H13] by lia.
              ** rewrite H5 in H13. rewrite H13. replace (a + (c' - a + 1))%nat with (S c') by lia. rewrite app_nth2 in H11; try lia. rewrite H13 in H11. rewrite H5 in H11. replace (c' - a + 1 - (c' - a + 1))%nat with 0%nat in H11 by lia.
                 simpl in H11. rewrite <- H11. tauto.
              ** apply H6; auto. split. lia. rewrite app_nth1 in H11; try lia. apply H11.
         * rewrite Forall_forall. intros x H9. repeat split.
           ++ inversion H9 as [H10 | H10]; try tauto. rewrite <- H10. auto.
           ++ inversion H9 as [H10 | H10]; try tauto. rewrite <- H10. tauto.
           ++ intros i [H10 H11]. simpl in H9. destruct H9 as [H9 | H9]; try tauto. rewrite <- H9. rewrite app_length in H10. rewrite H5 in H10. simpl in H10.
              assert (i = (c' - a + 1) \/ i < (c' - a + 1))%nat as [H12 | H12] by lia.
              ** rewrite H12. replace (a + (c' - a + 1))%nat with (S c') by lia. tauto.
              ** specialize (H6 x). rewrite app_nth1 in H11; try lia. assert (In x l2) as H13. { rewrite <- H5 in H12. apply nth_In with (d := []) in H12. rewrite H11 in H12. auto. }
                 specialize (H6 H13). rewrite H9. apply H6. split. lia. apply H11.
Qed.

Lemma test_lemmos2 : forall (m n : nat),
  (m >= 2)%nat ->
  (forall j : nat, (2 <= j <= m + 1)%nat -> exists l : list R, length l = m /\ Forall rational l /\ choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j)) = sum_f 0 (m - 1) (fun i : nat => nth i l 0 * INR n ^ (i + 1))) ->
    exists l1 : list (list R), (length l1 = m)%nat /\ Forall (fun l2 : list R => length l2 = m /\ Forall rational l2 /\ (forall (i : nat), nth i l1 [] = l2 -> choose (m + 1) (i+2) * sum_f 1 n (fun k : nat => INR k ^ (m + 1 - (i+2))) = sum_f 0 (m - 1) (fun i : nat => nth i l2 0 * INR n ^ (i + 1)))) l1.
Proof.
  intros m n H1 H2. set (f := fun j l => choose (m + 1) j * sum_f 1 n (fun i => INR i ^ (m + 1 - j)) = sum_f 0 (m - 1) (fun i => nth i l 0 * INR n ^ (i + 1))).
  assert (H3: forall b : nat, (2 <= b <= m + 1)%nat -> exists l1 : list R, length l1 = m /\ Forall rational l1 /\ f b l1). { intros b H3. apply H2 in H3 as [l [H3 H4]]. exists l. split; tauto. }
  pose proof (test_lemma2 2 (m + 1) m f) as H4. assert (H5 : (2 <= m + 1)%nat) by lia. specialize (H4 H5 H3). destruct H4 as [l1 H4]. exists l1. rewrite Forall_forall. split. destruct H4; lia.
  intros x H6. destruct H4 as [H4 H7]. repeat split.
  - rewrite Forall_forall in H7. specialize (H7 x H6). tauto.
  - rewrite Forall_forall in H7. specialize (H7 x H6). tauto.
  -  intros i H8. assert (i >= length l1 \/ i < length l1)%nat as [H9 | H9] by lia. rewrite nth_overflow in H8; try lia. rewrite Forall_forall in H7. specialize (H7 x H6) as [H7 H10]. 
    assert (length x = 0)%nat as H11. { rewrite length_zero_iff_nil. auto. } lia.
    rewrite Forall_forall in H7. specialize (H7 x H6) as [H7 [H10 H11]]. specialize (H11 i). assert ((0 <= i < length l1)%nat /\ nth i l1 [] = x) as H12. { split; auto; try lia. } apply H11 in H12. 
    unfold f in H12. replace (i + 2)%nat with (2 + i)%nat by lia. auto.
Qed.

Definition add_lists (l1 l2 : list R) : list R := map (fun p => fst p + snd p) (combine l1 l2).

Lemma add_lists_length : forall (l1 l2 : list R),
  length (add_lists l1 l2) = min (length l1) (length l2).
Proof.
  intros l1 l2. unfold add_lists. rewrite map_length. rewrite combine_length. lia.
Qed.

Lemma add_lists_separate : forall (l1 l2 : list R) (k m : nat),
  (0 <= k <= m-1)%nat -> length l1 = m -> length l2 = m -> nth k (add_lists l1 l2) 0 = nth k l1 0 + nth k l2 0.
Proof.
  intros l1 l2 k m H1 H2 H3. unfold add_lists. set (f := fun p : (R * R) => fst p + snd p). replace 0 with (f (0, 0)). 2 : { compute. lra. }
  rewrite map_nth. rewrite combine_nth; try lia. unfold f. simpl. replace (0 + 0) with 0 by lra. reflexivity.
Qed.

Lemma firstn_repeat_le : forall (n m : nat) (p : R),
  (n <= m)%nat -> firstn n (repeat p m) = repeat p n.
Proof.
  intros n m p H1. generalize dependent m. induction n as [| n' IH].
  - intros m H1. simpl. reflexivity.
  - intros m H1. destruct m as [| m'].
    -- inversion H1.
    -- simpl. simpl in H1. apply le_S_n in H1. rewrite IH; try lia. reflexivity.
Qed.

Lemma repeat_cons_prime : forall (a : R) (n : nat),
  a :: repeat a n = repeat a (n + 1).
Proof.
  intros a n. replace (n + 1)%nat with (S n) by lia. reflexivity.
Qed.

Lemma add_lists_repeat_0 : forall (l : list R) (m : nat),
  (length l <= m)%nat -> add_lists l (repeat 0 m) = l.
Proof.
  intros l m H1. generalize dependent l. induction m as [| m' IH].
  - intros l H1. simpl. assert (l = []) by (destruct l; auto; inversion H1). rewrite H. reflexivity.
  - intros l H1. assert (length l = S m' \/ length l <= m')%nat as [H2 | H2] by lia.
    -- destruct l. inversion H2. simpl in *. unfold add_lists in *. simpl. rewrite IH; try lia. replace (r + 0) with r by lra. reflexivity.
    -- unfold add_lists in *. simpl. rewrite combine_firstn_l. rewrite repeat_cons_prime. rewrite firstn_repeat_le; try lia.
       specialize (IH l H2). rewrite combine_firstn_l in IH. rewrite firstn_repeat_le in IH; try lia. rewrite IH. reflexivity. 
Qed.

Lemma add_lists_cons : forall (l1 l2 : list R) (a b : R),
  add_lists (a :: l1) (b :: l2) = (a + b) :: add_lists l1 l2.
Proof.
  intros l1 l2 a b. unfold add_lists. simpl. reflexivity.
Qed.

Lemma add_lists_comm : forall (l1 l2 : list R),
  add_lists l1 l2 = add_lists l2 l1.
Proof.
  intros l1 l2. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2. simpl. destruct l2; reflexivity.
  - intros l2. destruct l2 as [| h2 t2].
    -- simpl. reflexivity.
    -- rewrite add_lists_cons. rewrite add_lists_cons. rewrite IH. rewrite Rplus_comm. reflexivity.
Qed.

Open Scope Z_scope.

Lemma x_neq_0_IZR_den_neq_0 : forall x y z,
  (x <> 0 /\ x = IZR y / IZR z)%R -> z <> 0. 
Proof.
  intros x y z [H1 H2]. assert (z <> 0 \/ z = 0) as [H3 | H3] by lia. auto. rewrite H3 in H2. rewrite Rdiv_0_r in H2. nra.
Qed.

Lemma x_neq_0_IZR_num_neq_0 : forall x y z,
  (x <> 0 /\ x = IZR y / IZR z)%R -> y <> 0.
Proof.
  intros x y z [H1 H2]. assert (y <> 0 \/ y = 0) as [H3 | H3] by lia. auto. rewrite H3 in H2. rewrite Rdiv_0_l in H2. nra.
Qed.

Lemma mult_rational : forall a b,
  rational a -> rational b -> rational (a * b).
Proof.
  intros a b [z1 [z2 H1]] [z3 [z4 H2]].
  assert (a = 0 \/ b = 0 \/ a <> 0 /\ b <> 0)%R as [H3 | [H3 | [H3 H4]]] by lra.
  - exists 0, 1. nra.
  - exists 0, 1. nra.
  - exists (z1 * z3). exists (z2 * z4). rewrite H1. rewrite H2. repeat rewrite mult_IZR. field.
    split; apply not_0_IZR.
    -- apply x_neq_0_IZR_den_neq_0 with (x := b) (y := z3) (z := z4). auto.
    -- apply x_neq_0_IZR_den_neq_0 with (x := a) (y := z1) (z := z2). auto.
Qed.

Lemma lemma_2_12_a : forall a b,
  rational a -> rational b -> rational (a + b).
Proof.
  intros a b [z1 [z2 H1]] [z3 [z4 H2]].
  assert ((a = 0 \/ b = 0 \/ a <> 0 /\ b <> 0)%R) as [H3 | [H3 | H3]] by lra.
  - exists z3. exists z4. nra.
  - exists z1. exists z2. nra.
  - assert (H4 : forall x y z, (x <> 0 /\ x = IZR y / IZR z)%R -> z <> 0).
    { intros x y z [H4 H5]. assert (z <> 0 \/ z = 0) as [H6 | H6] by lia. auto. rewrite H6 in H5. rewrite Rdiv_0_r in H5. nra. }
    assert (H5 : z2 <> 0 /\ z4 <> 0). { split. apply H4 with (x := a) (y := z1). tauto. apply H4 with (x := b) (y := z3). tauto. }
    unfold rational. exists (z1 * z4 + z3 * z2). exists (z2 * z4). rewrite H1. rewrite H2. rewrite plus_IZR.
    repeat rewrite mult_IZR. field; split; apply not_0_IZR; lia.
Qed.

Close Scope Z_scope.

Lemma add_lists_rational : forall (l1 l2 : list R),
  Forall rational l1 -> Forall rational l2 -> Forall rational (add_lists l1 l2).
Proof.
  intros l1 l2 H1 H2. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2 H2. simpl. apply Forall_nil.
  - intros l2 H2. destruct l2 as [| h2 t2].
    -- apply Forall_nil.
    -- rewrite add_lists_cons. apply Forall_cons. apply lemma_2_12_a; apply Forall_inv in H1, H2; auto. apply IH. apply Forall_inv_tail in H1. apply Forall_inv_tail in H2. auto.
       apply Forall_inv_tail in H2. auto.
Qed.

Lemma fold_left_add_lists_length : forall (l1 : list (list R)) (l2 : list R) (m : nat),
  (forall l3, In l3 l1 -> length l3 = m) -> (length l2 = m) -> length (fold_left add_lists l1 l2) = m.
Proof.
  intros l1 l2 m H1 H2. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2 H2. simpl. apply H2.
  - intros l2 H2. simpl. apply IH. intros l3 H3. apply H1. right. apply H3. rewrite <- H2.
    rewrite add_lists_length. specialize (H1 h1). rewrite H1. lia. left. reflexivity.
Qed.

Lemma fold_left_add_lists_rational : forall (l1 : list (list R)) (l2 : list R),
  Forall (fun l : list R => Forall rational l) l1 -> Forall rational l2 -> Forall rational (fold_left add_lists l1 l2).
Proof.
  intros l1 l2 H1 H2. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2 H2. simpl. apply H2.
  - intros l2 H2. simpl. apply IH.
    + apply Forall_forall. intros x H3. apply Forall_cons_iff in H1 as [H1 H4]. apply Forall_forall. intros y H5. rewrite (Forall_forall) in H4.
      specialize (H4 x H3). rewrite Forall_forall in H4. specialize (H4 y H5). tauto.
    + apply add_lists_rational; try apply Forall_inv in H1; try apply Forall_inv_tail in H1; auto.
Qed.

Lemma add_lists_nil : forall (l : list R),
  add_lists l [] = [].
Proof.
  intros l. unfold add_lists. rewrite combine_nil. simpl. reflexivity.
Qed.

Lemma add_lists_assoc : forall l1 l2 l3 : list R,
  add_lists l1 (add_lists l2 l3) = add_lists (add_lists l1 l2) l3.
Proof.
  intros l1 l2 l3. generalize dependent l2. generalize dependent l1. induction l3 as [| h3 t3 IH].
  - intros l1 l2. repeat rewrite add_lists_nil. reflexivity.
  - intros l1 l2. destruct l1 as [| h1 t1].
    -- simpl. reflexivity.
    -- destruct l2 as [| h2 t2].
      ++ simpl. reflexivity.
      ++ rewrite add_lists_cons. rewrite add_lists_cons. rewrite add_lists_cons. rewrite add_lists_cons. rewrite IH. rewrite Rplus_assoc. reflexivity.
Qed.

Lemma fold_left_add_lists_symmetric : forall (l1 : list (list R)) (l2 : list R),
  fold_left add_lists l1 l2 = fold_right add_lists l2 l1.
Proof.
  intros l1 l2; apply fold_symmetric; try apply add_lists_assoc; try apply add_lists_comm.
Qed.

Fixpoint min_list_len (l : list (list R)) : nat :=
  match l with
  | [] => 0
  | x :: nil => length x
  | x :: xs => min (length x) (min_list_len xs)
  end.

Lemma fold_left_add_lists_length' : forall (l1 : list (list R)) (l2 : list R),
  length (fold_left add_lists l1 l2) = min_list_len (l2 :: l1).
Proof.
  intros l1 l2. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2. simpl. reflexivity.
  - intros l2. simpl. rewrite IH. destruct t1 as [| h2 t2].
    -- simpl. rewrite add_lists_length. rewrite Nat.min_comm. reflexivity.
    -- simpl. rewrite add_lists_length. rewrite Nat.min_assoc. reflexivity.
Qed.

Lemma fold_right_min_0 : forall (l : list (list R)),
  fold_right (fun x y => min (length x) y) 0%nat l = 0%nat.
Proof.
  intros l. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma min_list_len_cons : forall (l1 : list R) (l2 : list (list R)),
  l2 <> [] -> min_list_len (l1 :: l2) = min (length l1) (min_list_len l2).
Proof.
  intros l1 l2 H1. destruct l2 as [| h2 t2].
  - destruct H1. reflexivity.
  - simpl. reflexivity.
Qed.

Lemma min_list_same_length : forall (l1 : list (list R)),
  (forall l2 l3, In l2 l1 -> In l3 l1 -> length l2 = length l3) -> min_list_len l1 = length (nth 0 l1 []).
Proof.
  intros l1 H1. induction l1 as [| h1 t1 IH].
  - simpl. reflexivity.
  - assert (t1 = [] \/ t1 <> []) as [H4 | H4] by tauto.
    -- rewrite H4. simpl. reflexivity.
    -- rewrite min_list_len_cons. 2 : { tauto. } simpl. rewrite IH. 2 : { intros l2 l3 H5 H6. apply H1. right. apply H5. right. apply H6. }
       specialize (H1 h1 (nth 0 t1 [])). rewrite H1. apply Nat.min_id. left. reflexivity. right. apply nth_In. assert (length t1 <> 0)%nat as H5.
       { rewrite length_zero_iff_nil. auto. } lia.
Qed.

Lemma min_list_cons_switch : forall l1 l2,
  min_list_len (l2 :: l1) = min_list_len (l1 ++ [l2]).
Proof.
  intros l1 l2. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2. simpl. reflexivity.
  - intros l2. assert (t1 = [] \/ t1 <> []) as [H1 | H1] by tauto.
    -- rewrite H1. simpl. rewrite Nat.min_comm. reflexivity.
    -- assert (H2 : h1 :: t1 <> []) by discriminate. assert (H3 : t1 ++ [l2] <> []). { intros H3. apply app_eq_nil in H3. tauto. }
       rewrite min_list_len_cons. 2 : { tauto. } rewrite min_list_len_cons. 2 : { tauto. }
       replace ((h1 :: t1) ++ [l2]) with (h1 :: (t1 ++ [l2])) by reflexivity. rewrite min_list_len_cons. 2 : { simpl. tauto. } rewrite <- IH.
       rewrite min_list_len_cons. 2 : { simpl. tauto. } rewrite Nat.min_assoc. rewrite Nat.min_comm. rewrite Nat.min_assoc.
       rewrite Nat.min_comm. rewrite Nat.min_comm with (n := length l2). reflexivity.
Qed.

Lemma fold_right_add_lists_length : forall (l1 : list (list R)) (l2 : list R),
  length (fold_right add_lists l2 l1) = min_list_len (l1 ++ [l2]).
Proof.
  intros l1 l2. rewrite <- fold_left_add_lists_symmetric. rewrite fold_left_add_lists_length'. 
  rewrite min_list_cons_switch. reflexivity.
Qed.

Lemma sum_f_nth : forall (l1 : list (list R)) (l2 : list R) (i : nat),
  nth i l2 0 + sum_f 0 (length l1 - 1) (fun j : nat => nth i (nth j l1 []) 0) = sum_f 0 (S (length l1 - 1)) (fun j : nat => nth i (nth j ([l2] ++ l1) []) 0).
Proof.
  intros l1 l2 i. assert (length l1 = 0 \/ length l1 > 0)%nat as [H1 | H1] by lia.
  - rewrite length_zero_iff_nil in H1. rewrite H1. simpl. rewrite sum_f_0_0. rewrite sum_f_Si; try lia. rewrite sum_f_n_n. lra.
  - rewrite sum_f_Si with (n := S (length l1 - 1)). 2 : { simpl. lia. } 
    replace (sum_f 1 (S (length l1 - 1)) (fun j : nat => nth i (nth j ([l2] ++ l1) []) 0)) with (sum_f 1 (S (length l1 - 1)) (fun j : nat => nth i (nth (j-1) l1 []) 0)).
    2 : { apply sum_f_congruence. 2 : { intros k H2. destruct k; simpl; try lia. rewrite Nat.sub_0_r. reflexivity. } lia. }
    replace (nth i (nth 0 ([l2] ++ l1) []) 0) with (nth i l2 0). 2 : { reflexivity. } rewrite sum_f_reindex with (s := 1%nat) (i := 1%nat). 2 : { simpl. lia. }
    replace (S (length l1 - 1)) with (length l1) by lia. replace (1-1)%nat with 0%nat by lia. replace ((fun x : nat => nth i (nth (x + 1 - 1) l1 []) 0)) with (fun x : nat => nth i (nth x l1 []) 0).
    2 : { apply functional_extensionality. intros x. replace (x + 1 - 1)%nat with x by lia. reflexivity. } lra.
Qed.

Lemma sum_f_nth_cons_0 : forall (l : list R) (r : R),
  (length l > 0)%nat -> sum_f 1 (length l) (fun i => nth i (r :: l) 0) = sum_f 0 (length l - 1) (fun i => nth i l 0).
Proof.
  intros l r H1. rewrite sum_f_reindex' with (s := 1%nat) (i := 0%nat). replace (length l - 1 + 1)%nat with (length l) by lia.
  apply sum_f_equiv; try lia. intros k H2. replace (r :: l) with ([r] ++ l) by reflexivity. rewrite app_nth2; try (simpl; lia). simpl. lra.
Qed.

Lemma sum_f_nth_cons_1 : forall {A : Type} (l : list R) (r : R) (f : R -> A -> R) (a : A),
  (length l > 0)%nat -> sum_f 0 (length l) (fun i => f (nth i (r :: l) 0) a) = f r a + sum_f 0 (length l - 1) (fun i => f (nth i l 0) a).
Proof.
  intros A l r f a H1.
  rewrite sum_f_Si with (n := length l); try lia. replace (sum_f 1 (length l) (fun i : nat => f (nth i (r :: l) 0) a)) with (sum_f 0 (length l - 1) (fun i => f (nth i l 0) a)).
  2 : { rewrite sum_f_reindex' with (s := 1%nat) (i := 0%nat). replace (length l - 1 + 1)%nat with (length l) by lia. apply sum_f_equiv; try lia. intros k H2. replace (r :: l) with ([r] ++ l) by reflexivity. rewrite app_nth2; try (simpl; lia). simpl. lra. }
  simpl. lra.
Qed.

Lemma sum_f_nth_cons_2 : forall {A : Type} (l : list R) (r : R) (f : R -> A -> R) (a : A),
  (length l > 0)%nat -> sum_f 1 (length l) (fun i => f (nth i (r :: l) 0) a) = sum_f 0 (length l - 1) (fun i => f (nth i l 0) a).
Proof.
  intros A l r f a H1.
  rewrite sum_f_reindex' with (s := 1%nat) (i := 0%nat). replace (length l - 1 + 1)%nat with (length l) by lia. apply sum_f_equiv; try lia. intros k H2. replace (r :: l) with ([r] ++ l) by reflexivity. rewrite app_nth2; try (simpl; lia). simpl. lra.
Qed.

Lemma sum_f_nth_cons_3 : forall (l1 l2 : list R) (r1 r2 : R),
  (length l1 = length l2)%nat -> sum_f 1 (length l1) (fun i => (r1 * nth i (r2 :: l2) 0 - r2 * nth i (r1 :: l1) 0)^2) = sum_f 0 (length l1 - 1) (fun i => (r1 * nth i l2 0 - r2 * nth i l1 0)^2).
Proof.
  intros l1 l2 r1 r2 H1. rewrite sum_f_reindex' with (s := 1%nat) (i := 0%nat). assert (length l1 = 0 \/ length l1 > 0)%nat as [H2 | H2] by lia.
  - rewrite H2. simpl. rewrite sum_f_Sn_n; try lia. rewrite sum_f_n_n. simpl. lra.
  - replace (length l1 - 1 + 1)%nat with (length l1) by lia. apply sum_f_equiv; try lia. intros k H3. replace (r1 :: l1) with ([r1] ++ l1) by reflexivity. replace (r2 :: l2) with ([r2] ++ l2) by reflexivity. rewrite app_nth2; try (simpl; lia). rewrite app_nth2; try (simpl; lia). simpl. lra.
Qed.

Lemma sum_f_nth_cons_4 : forall (l1 l2 : list R) (r1 r2 : R),
  (length l1 = length l2)%nat -> sum_f 1 (length l1) (fun i => (r1 * nth i (r2 :: l2) 0) ^ 2 - r1 * r2 * nth i (r1 :: l1) 0 * nth i (r2 :: l2) 0) = sum_f 0 (length l1 - 1) (fun i => ((r1 * nth i l2 0) ^ 2 - r1 * r2 * nth i l1 0 * nth i l2 0)).
Proof.
  intros l1 l2 r1 r2 H1. rewrite sum_f_reindex' with (s := 1%nat) (i := 0%nat). assert (length l1 = 0 \/ length l1 > 0)%nat as [H2 | H2] by lia.
  - rewrite H2. simpl. rewrite sum_f_Sn_n; try lia. rewrite sum_f_n_n. simpl. lra.
  - replace (length l1 - 1 + 1)%nat with (length l1) by lia. apply sum_f_equiv; try lia. intros k H3. replace (r1 :: l1) with ([r1] ++ l1) by reflexivity. replace (r2 :: l2) with ([r2] ++ l2) by reflexivity. rewrite app_nth2; try (simpl; lia). rewrite app_nth2; try (simpl; lia). simpl. lra.
Qed.
  
Lemma nth_fold_right_add_lists : forall (l1 : list (list R)) (i : nat),
  (forall x1 x2 : list R, In x1 l1 -> In x2 l1 -> length x1 = length x2) -> nth i (fold_right add_lists (repeat 0 (length (nth 0 l1 []))) l1) 0 = sum_f 0 (length l1 - 1) (fun j : nat => nth i (nth j l1 []) 0).
Proof.
  intros l1 i H1. induction l1 as [| h1 t1 IH].
  - destruct i; reflexivity.
  - replace (h1 :: t1) with ([h1] ++ t1) by reflexivity. rewrite fold_right_app.
    assert (t1 = [] \/ t1 <> []) as [H2 | H2] by tauto.
    -- rewrite H2. simpl. rewrite sum_f_0_0. rewrite add_lists_repeat_0. 2 : { lia. } simpl. lra.
    -- assert (length t1 <> 0)%nat as H3. { rewrite length_zero_iff_nil; auto. } assert (i >= length h1 \/ i < length h1)%nat as [H4 | H4] by lia.
       { rewrite nth_overflow.
         2 : { simpl. rewrite add_lists_length. rewrite fold_right_add_lists_length. rewrite <- min_list_cons_switch. rewrite min_list_len_cons; auto. rewrite repeat_length.
               rewrite min_list_same_length. 2 : { intros l2 l3 H5 H6. apply H1; (right; auto). } replace (length (nth 0 t1 [])) with (length h1).
               2 : { specialize (H1 h1 (nth 0 t1 [])). apply H1. left. reflexivity. right. apply nth_In. lia. } rewrite Nat.min_id. lia. 
             }
         replace (sum_f 0 (length ([h1] ++ t1) - 1) (fun j : nat => nth i (nth j ([h1] ++ t1) []) 0)) with (sum_f 0 (length ([h1] ++ t1) - 1) (fun j : nat => 0)).
         2 : { apply sum_f_equiv; try lia. intros k H5. rewrite nth_overflow. reflexivity. specialize (H1 (nth k ([h1] ++ t1) []) h1).
               assert (H6 : In (nth k ([h1] ++ t1) []) (h1 :: t1)). { apply nth_In. simpl in *. lia. } assert (H7 : In h1 (h1 :: t1)). { left. reflexivity. } rewrite (H1 H6 H7). lia. }
         rewrite sum_f_const. lra.
       }
    replace (nth i (fold_right add_lists (fold_right add_lists (repeat 0 (length (nth 0 ([h1] ++ t1) []))) t1) [h1]) 0) with (nth i (add_lists h1 (fold_right add_lists (repeat 0 (length h1)) t1)) 0) by reflexivity.
       
    rewrite add_lists_separate with (m := length h1). 
    4 : { rewrite <- fold_left_add_lists_symmetric. rewrite fold_left_add_lists_length'; try lia. rewrite min_list_len_cons; try tauto. rewrite repeat_length. rewrite min_list_same_length.
          2 : { intros l2 l3 H5 H6. apply H1; (right; auto). } replace (length h1) with (length (nth 0 (t1) [])). 2 : { apply H1. right. apply nth_In. lia. left. reflexivity. } apply Nat.min_id. }
    2 : { lia.  }
    2 : { reflexivity. }
    replace (length h1) with (length (nth 0 t1 [])). 2 : { apply H1. right. apply nth_In. lia. left. reflexivity. }
    rewrite IH. 2 : { intros x1 x2 H5 H6. apply H1; (right; auto). }
    replace (length ([h1] ++ t1) - 1)%nat with (S (length t1 - 1)) by (simpl; lia). rewrite sum_f_nth; try lia. reflexivity.
Qed.

Lemma nth_fold_left_add_lists : forall (l1 : list (list R)) (i : nat),
  (forall x1 x2 : list R, In x1 l1 -> In x2 l1 -> length x1 = length x2) -> nth i (fold_left add_lists l1 (repeat 0 (length (nth 0 l1 [])))) 0 = sum_f 0 (length l1 - 1) (fun j : nat => nth i (nth j l1 []) 0).
Proof.
  intros l1 i H1. rewrite fold_left_add_lists_symmetric. apply nth_fold_right_add_lists; auto.
Qed.

Lemma In_repeat : forall (A : Type) (a b : A) (n : nat),
  (n >= 1)%nat -> In a (repeat b n) -> a = b.
Proof.
  intros A a b n H1 H2. induction n as [| n' IH].
  - inversion H1.
  - assert (S n' = 1 \/ S n' > 1)%nat as [H3 | H3] by lia.
    -- rewrite H3 in H2. simpl in H2. destruct H2 as [H2 | H2]; try tauto. rewrite H2. reflexivity.
    -- simpl in H2. destruct H2 as [H2 | H2]; try tauto. auto. apply IH; try lia; auto.
Qed.

Lemma add_lists_sum_f : forall (m n : nat),
  (m >= 2)%nat -> (n >= 1)%nat -> (exists l1 : list (list R), length l1 = m /\ Forall (fun l2 : list R => length l2 = m /\ Forall rational l2 /\ (forall i : nat, nth i l1 [] = l2 -> choose (m + 1) (i + 2) * sum_f 1 n (fun k : nat => INR k ^ (m + 1 - (i + 2))) = sum_f 0 (m - 1) (fun i0 : nat => nth i0 l2 0 * INR n ^ (i0 + 1)))) l1)
    -> exists l : list R, length l = m /\ Forall rational l /\ sum_f 2 (m + 1) (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j))) = sum_f 0 (m - 1) (fun i : nat => nth i l 0 * INR n ^ (i + 1)).
Proof.
  intros m n H1 H2 H3. destruct H3 as [l1 [H3 H4]]. rewrite Forall_forall in H4.
  exists (fold_left add_lists l1 (repeat 0 m)). repeat split.
  - apply fold_left_add_lists_length with (m := m); try lia. intros l2 H5. apply H4. apply H5. rewrite repeat_length. reflexivity.
  - apply fold_left_add_lists_rational. apply Forall_forall. intros x H5. specialize (H4 x). apply H4. apply H5. apply Forall_forall. intros x H5. apply In_repeat in H5; try lia.
    exists (0%Z), (1%Z). lra.
  - rewrite sum_f_reindex with (s := 2%nat); try lia. replace (2 - 2)%nat with 0%nat by lia. replace (m + 1 - 2)%nat with (m - 1)%nat by lia.
    replace (sum_f 0 (m - 1) (fun i : nat => nth i (fold_left add_lists l1 (repeat 0 m)) 0 * INR n ^ (i + 1))) with (sum_f 0 (m - 1) (fun i : nat => sum_f 0 (m - 1) (fun j : nat => nth i (nth j l1 []) 0) * INR n ^ (i + 1))).
    2 : { apply sum_f_equiv; try lia. intros i H5. rewrite <- H3 at 2. replace (length l1) with (length (nth 0 l1 [])). 2 : { specialize (H4 (nth 0 l1 [])). assert (H6 : In (nth 0 l1 []) l1). apply nth_In. lia. apply H4 in H6. lia. }
    rewrite nth_fold_left_add_lists; try lia. 2 : { intros x1 x2 H6 H7. apply H4 in H6 as [H6 H8]. apply H4 in H7 as [H7 H9]. lia. }
          specialize (H4 (nth i l1 [])). assert (In (nth i l1 []) l1) as H6. { apply nth_In. rewrite H3. lia. } rewrite H3. reflexivity. }
    replace (sum_f 0 (m - 1) (fun x : nat => choose (m + 1) (x + 2) * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - (x + 2))))) with (sum_f 0 (m-1) (fun x : nat => sum_f 0 (m-1) (fun j : nat => nth j (nth (x) l1 []) 0 * INR n ^ (j + 1)))).
    2 : { apply sum_f_equiv; try lia. intros i H5. specialize (H4 (nth i l1 [])). assert (In (nth i l1 []) l1) as H6. { apply nth_In. rewrite H3. lia. } apply H4 in H6 as [H6 [H7 H8]].
    specialize (H8 i). assert (nth i l1 [] = nth i l1 []) as H9 by reflexivity. apply H8 in H9. rewrite H9. reflexivity. }
    rewrite sum_swap; try lia. apply sum_f_equiv; try lia. intros i H5. rewrite <- r_mult_sum_f_i_n_f. apply Rmult_comm.
Qed.

Lemma lemma_2_7 : forall n p,
  (n >= 1)%nat -> (p >= 1)%nat ->
    exists l : list R,
      length l = p /\ Forall rational l /\ sum_f 1 n (fun i => INR i ^ p) = INR n ^ (p + 1) / INR (p + 1) + sum_f 0 (p-1) (fun i => nth i l 0 * INR n ^ (i + 1)).
Proof.
  intros n p H1 H2. apply strong_induction_N with (n := p).
  intros m IH. assert (m = 0 \/ m = 1 \/ m >= 2)%nat as [H3 | [H3 | H3]] by lia.
  - rewrite H3. simpl. rewrite sum_f_const. exists []. rewrite sum_f_0_0. simpl. rewrite plus_INR.
    rewrite minus_INR; try lia. simpl. repeat split; try lra. apply Forall_nil.
  - rewrite H3. replace ((fun i => INR i ^ 1)) with (fun i => INR i) by (apply functional_extensionality; intros; lra).
    rewrite sum_n_nat; auto. exists [1/2]. rewrite sum_f_0_0. simpl. repeat split; try lra. apply Forall_cons; try apply Forall_nil. exists (1%Z), (2%Z). reflexivity.
  - assert (H4 : forall k, (INR k + 1)^(m+1) - (INR k)^(m+1) = sum_f 2 (m+1) (fun i => choose (m+1) i * (INR k)^(m+1-i)) + INR (m + 1) * INR k ^ m).
    {
      intros k. rewrite lemma_2_3_d. rewrite sum_f_Si; try lia. rewrite n_choose_0. simpl. rewrite Rmult_1_r. rewrite Rmult_1_l. 
      replace (m+1-0)%nat with (m+1)%nat by lia. unfold Rminus. rewrite Rplus_assoc.
      field_simplify. rewrite sum_f_Si; try lia. rewrite n_choose_1. replace (m + 1 - 1)%nat with m by lia. replace (INR (m + 1) * INR k ^ m * 1 ^ 1) with (INR (m + 1) * INR k ^ m) by (simpl; lra).
        apply Rplus_eq_compat_r. apply sum_f_equiv; try lia. intros k2 H5. rewrite pow1. rewrite Rmult_1_r. reflexivity. 
    }
    assert (H5 : sum_f 1 n (fun i => (INR i + 1) ^ (m + 1) - INR i ^ (m + 1)) = (INR n + 1)^(m+1) - 1).
    {
      set (f := fun x => INR x ^ (m+1)). replace ((INR n + 1) ^ (m + 1)) with (f (n+1)%nat).
      2 : { unfold f. rewrite plus_INR. reflexivity. }
      replace 1 with (f 1%nat).
      2 : { unfold f. simpl. rewrite pow1. reflexivity. }
      rewrite <- sum_f_1_n_fSi_minus_fi with (n := n) (f := f); try lia. apply sum_f_equiv; try lia. intros k H5.
      unfold f. rewrite plus_INR. simpl. rewrite pow1. reflexivity.
    }
    assert (H6 : sum_f 1 n (fun i => (INR i + 1)^(m+1) - (INR i)^(m+1)) = sum_f 1 n (fun i => sum_f 2 (m+1) (fun j => choose (m+1) j * (INR i)^(m+1-j)) + INR (m + 1) * INR i ^ m)).
    { apply sum_f_equiv; try lia. intros k H6. specialize (H4 k). rewrite <- H4. lra. } rewrite H5 in H6. rewrite <- sum_f_plus in H6; try lia. rewrite <- r_mult_sum_f_i_n_f_l in H6.
    rewrite Rplus_comm in H6. rewrite lemma_2_3_d in H6. replace ((fun i : nat => choose (m + 1) i * 1 ^ (m + 1 - i) * INR n ^ i)) with 
    (fun i : nat => choose (m + 1) i * INR n ^ i) in H6. 2 : { apply functional_extensionality. intros. rewrite pow1. lra. }
    rewrite sum_f_Si in H6; try lia. rewrite n_choose_0 in H6. simpl in H6. rewrite Rmult_1_r in H6. field_simplify in H6.
    replace (m + 1)%nat with (S m) in H6 at 1 by lia. rewrite sum_f_i_Sn_f in H6; try lia. replace (S m) with (m + 1)%nat in H6 by lia.
    rewrite n_choose_n in H6. field_simplify in H6. rewrite sum_swap in H6; try lia. replace (fun j : nat => sum_f 1 n (fun i : nat => choose (m + 1) j * INR i ^ (m + 1 - j))) with 
    (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j))) in H6. 2 : { apply functional_extensionality. intros. apply r_mult_sum_f_i_n_f_l. }
    assert (H7 : INR (m + 1) * sum_f 1 n (fun i : nat => INR i ^ m) = INR n ^ (m + 1) + sum_f 1 m (fun i : nat => choose (m + 1) i * INR n ^ i) - sum_f 2 (m + 1) (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j)))) by nra.
    assert (H8 : sum_f 1 n (fun i : nat => INR i ^ (m)) = INR n ^ (m + 1) / INR (m + 1) + (sum_f 1 m (fun i : nat => choose (m + 1) i * INR n ^ i) / INR (m + 1) - sum_f 2 (m + 1) (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j))) / INR (m + 1))). 
    { apply Rmult_eq_reg_l with (r := INR (m + 1)). rewrite H7. field. apply not_0_INR. lia. apply not_0_INR. lia. }
    rewrite H8. apply exist_R_plus_eq_l. assert (H9 : forall j : nat, (2 <= j <= m + 1)%nat -> exists l : list R, length l = m%nat /\ Forall rational l /\ sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j)) = sum_f 0 (m-1) (fun i : nat => nth i l 0 * INR n ^ (i+1))).
    {
      intros j [H9 H10]. specialize (IH (m + 1 - j)%nat). assert (H11 : (m + 1 - j < m)%nat) by lia. apply IH in H11. destruct H11 as [l [H11 [H12' H12]]]. rewrite H12.
      exists (l ++ [1 / INR (m + 1 - j + 1)] ++ repeat 0 (j - 2)). assert (j = 2 \/ j > 2)%nat as [H13 | H13] by lia; assert (j = m + 1 \/ j < m + 1)%nat as [H14 | H14] by lia; try lia.
      - rewrite H13 in *. simpl. replace (m + 1 - 2 + 1)%nat with m by lia. replace (m + 1 - 2 - 1)%nat with (m - 2)%nat by lia.
        replace (m - 1)%nat with (S (m - 2)) by lia. rewrite sum_f_i_Sn_f with (n := (m - 2)%nat); try lia.
        replace (sum_f 0 (m - 2) (fun i : nat => nth i (l ++ [1 / INR m]) 0 * INR n ^ (i + 1))) with (sum_f 0 (m - 2) (fun i : nat => nth i l 0 * INR n ^ (i + 1))).
        2 : { apply sum_f_equiv; try lia. intros k H15. rewrite app_nth1; try lia. reflexivity. } replace (nth (S (m - 2)) (l ++ [1 / INR m]) 0) with (1 / INR m).
        2 : { rewrite app_nth2; try lia. rewrite H11. replace (S (m - 2) - (m + 1 - 2))%nat with 0%nat by lia. simpl. reflexivity. } replace (S (m - 2) + 1)%nat with m by lia. repeat split. rewrite app_length. rewrite H11. simpl. lia.
              apply Forall_app. split. apply H12'. apply Forall_cons. exists (1%Z), (Z.of_nat m). rewrite INR_IZR_INZ. reflexivity. apply Forall_nil.
        field. apply not_0_INR. lia.
      - rewrite H14 in *. replace (m + 1 - (m + 1) + 1)%nat with 1%nat by lia. replace (INR n ^ 1 / INR 1) with (INR n) by (simpl; field).
        replace (m + 1 - (m + 1) - 1)%nat with 0%nat by lia. assert (H15 : l = []) by (apply length_zero_iff_nil; lia). rewrite H15.
        rewrite sum_f_0_0. replace ((fun i : nat => nth i ([] ++ [1 / INR 1] ++ repeat 0 (m + 1 - 2)) 0 * INR n ^ (i + 1))) with (fun i : nat => nth i [1 / INR 1] 0 * INR n ^ (i + 1)).
        2 : { apply functional_extensionality. intros k. rewrite app_nth2. 2 : { simpl. lia. } replace (k - length [])%nat with k. 2 : { simpl. lia. } 
              assert (k = 0 \/ k > 0)%nat as [H16 | H16] by lia. rewrite H16. simpl. reflexivity. assert (k <= m \/ k > m)%nat as [H17 | H17] by lia.
              - rewrite nth_overflow. 2 : { simpl. lia. } rewrite app_nth2. 2 : { simpl. lia. } simpl. rewrite nth_repeat. reflexivity.
              - rewrite nth_overflow. 2 : { simpl. lia. } rewrite app_nth2. 2 : { simpl. lia. } simpl. rewrite nth_repeat. reflexivity.
            }
            rewrite sum_f_Si. 2 : { lia. } replace (sum_f 1 (m - 1) (fun i : nat => nth i [1 / INR 1] 0 * INR n ^ (i + 1))) with (sum_f 1 (m -1) (fun i => 0)).
            2 : { apply sum_f_equiv; try lia. intros k H16. rewrite nth_overflow. 2 : { simpl. lia. } lra. } simpl. rewrite sum_f_const. repeat split. rewrite repeat_length. lia. 2 : lra.
            apply Forall_forall. intros x H16. inversion H16 as [H17 | H18]. exists (1%Z), (1%Z). auto. exists (0%Z), (1%Z). apply In_repeat with (n := (m + 1 - 2)%nat); try lia. replace (0 / 1) with 0 by lra. auto.
      - replace (m + 1 - j - 1)%nat with (m - j)%nat by lia. replace (m + 1 - j + 1)%nat with (m - j + 2)%nat by lia. assert (0 = m - j \/ 0 < m - j)%nat as [H15 | H15] by lia.
        -- rewrite <- H15. rewrite sum_f_0_0. simpl. assert (H16 : length l = 1%nat) by lia. rewrite sum_f_Si; try lia. replace (sum_f 1 (m - 1) (fun i : nat => nth i (l ++ 1 / (1 + 1) :: repeat 0 (j - 2)) 0 * INR n ^ (i + 1))) with (INR n * INR n / 2).
           2 : { rewrite sum_f_Si; try lia. replace (nth 1 (l ++ 1 / (1 + 1) :: repeat 0 (j - 2)) 0) with (1 / 2). 2 : { rewrite app_nth2; try lia. rewrite H16. simpl. reflexivity. }
                 replace (sum_f 2 (m - 1) (fun i : nat => nth i (l ++ 1 / (1 + 1) :: repeat 0 (j - 2)) 0 * INR n ^ (i + 1))) with (sum_f 2 (m - 1) (fun i : nat => 0)).
                 2 : { apply sum_f_equiv; try lia. intros k H17. rewrite app_nth2; try lia. rewrite H16. replace (1 / (1 + 1) :: repeat 0 (j - 2)) with ([1 / 2] ++ repeat 0 (j - 2)) by reflexivity.
                       rewrite app_nth2. 2 : { simpl. lia. } simpl. rewrite nth_repeat. lra. }
                 simpl. rewrite sum_f_const. lra.
               }
            simpl. rewrite app_nth1; try lia. repeat split. repeat rewrite app_length. simpl. rewrite repeat_length. lia.
            apply Forall_app. split. apply H12'. apply Forall_cons. exists (1%Z), (2%Z). reflexivity. apply Forall_forall. intros x H17. exists (0%Z), (1%Z). apply In_repeat with (n := (j - 2)%nat); try lia. replace (0 / 1) with 0 by lra. auto.
             lra.
        -- rewrite sum_f_split with (l := 0%nat) (m := (m -1)%nat) (n := (m-j)%nat); try lia. replace (sum_f 0 (m - j) (fun i : nat => nth i (l ++ [1 / INR (m - j + 2)] ++ repeat 0 (j - 2)) 0 * INR n ^ (i + 1))) with (sum_f 0 (m - j) (fun i : nat => nth i l 0 * INR n ^ (i + 1))).
           2 : { apply sum_f_equiv; try lia. intros k H16. rewrite app_nth1; try lia. reflexivity. } replace (sum_f (S (m - j)) (m - 1) (fun i : nat => nth i (l ++ [1 / INR (m - j + 2)] ++ repeat 0 (j - 2)) 0 * INR n ^ (i + 1))) with (INR n ^ (m - j + 2) / INR (m - j + 2)).
           2 : { rewrite sum_f_Si_n_f; try lia. replace (nth (m - j) (l ++ [1 / INR (m - j + 2)] ++ repeat 0 (j - 1)) 0 * INR n ^ (m - j + 1)) with (nth (m-j) l 0 * INR n ^ (m - j + 1)).
                2 : { rewrite app_nth1; try lia. lra. } rewrite sum_f_Si; try lia. replace (nth (m - j) (l ++ [1 / INR (m - j + 2)] ++ repeat 0 (j - 2)) 0 * INR n ^ (m - j + 1)) with (nth (m - j) l 0 * INR n ^ (m - j + 1)).
                2 : { rewrite app_nth1; try lia. lra. } field_simplify. 2 : { apply not_0_INR. lia. } rewrite sum_f_Si; try lia.
                replace (nth (S (m - j)) (l ++ [1 / INR (m - j + 2)] ++ repeat 0 (j - 2)) 0 * INR n ^ (S (m - j) + 1)) with (INR n ^ (m - j + 2) / INR (m - j + 2)).
                2 : { rewrite app_nth2; try lia. rewrite H11. replace (S (m - j) - (m + 1 - j))%nat with 0%nat by lia. simpl. rewrite <- pow_1 with (x := INR n) at 2. rewrite <- pow_add. replace (1 + (m - j + 1))%nat with (m - j + 2)%nat by lia. lra. }
                replace (sum_f (S (S (m - j))) (m - 1) (fun i : nat => nth i (l ++ [1 / INR (m - j + 2)] ++ repeat 0 (j - 2)) 0 * INR n ^ (i + 1))) with (sum_f (S (S (m - j))) (m - 1) (fun i : nat => 0)).
                2 : { apply sum_f_equiv; try lia. intros k H17. rewrite app_nth2; try lia. rewrite H11. rewrite app_nth2. 2 : { simpl. lia. } simpl. rewrite nth_repeat. lra. }
                rewrite sum_f_const. lra.
           }
           repeat split. repeat rewrite app_length. rewrite H11. rewrite repeat_length. simpl. lia.
           apply Forall_app. split. apply H12'. apply Forall_cons. exists (1%Z), (Z.of_nat (m - j + 2)). rewrite INR_IZR_INZ. reflexivity. apply Forall_forall. intros x H16. exists (0%Z), (1%Z). apply In_repeat with (n := (j - 2)%nat); try lia. replace (0 / 1) with 0 by lra. auto.
            lra.
    }
    assert (H10 : forall j : nat, (2 <= j <= m + 1)%nat -> exists l : list R, length l = m /\ Forall rational l /\ choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j)) = sum_f 0 (m - 1) (fun i : nat => nth i l 0 * INR n ^ (i + 1))). 
    {
      intros j H10. specialize (H9 j). apply H9 in H10 as [l [H10 [H11 H12]]]. exists (map (Rmult (choose (m + 1) j)) l). repeat split. rewrite map_length. apply H10.
      apply Forall_forall. intros x H13. rewrite Forall_forall in H11. apply in_map_iff in H13 as [x' [H13 H14]]. rewrite <- H13. apply H11 in H14. pose proof (choose_rational (m + 1) j) as H15. apply mult_rational; auto.
       rewrite H12. 
      replace ((fun i : nat => nth i (map (Rmult (choose (m + 1) j)) l) 0 * INR n ^ (i + 1))) with ((fun i : nat => choose (m + 1) j * (nth i l 0) * INR n ^ (i + 1))).
      2 : { apply functional_extensionality. intros k. rewrite <- map_nth. rewrite Rmult_0_r. reflexivity. }
      rewrite r_mult_sum_f_i_n_f_l. apply sum_f_equiv; try lia. intros k H13. lra. 
    }
    assert (H11 : exists l : list R, length l = m /\ Forall rational l /\ sum_f 1 m (fun i : nat => choose (m + 1) i * INR n ^ i) = sum_f 0 (m - 1) (fun i : nat => nth i l 0 * INR n ^ (i + 1))).
    { exists (build_list_for_lemma_2_7 m m). repeat split. apply build_list_for_lemma_2_7_length. apply build_list_for_lemma_2_7_rational. apply build_list_for_lemma_2_7_sum; lia. }

    assert (H12 : exists l : list R, length l = m /\ Forall rational l /\ sum_f 1 m (fun i : nat => choose (m + 1) i * INR n ^ i) / INR (m + 1) = sum_f 0 (m - 1) (fun i : nat => nth i l 0 * INR n ^ (i + 1))).
    { 
      destruct H11 as [l [H11 [H12 H13]]]. exists (map (Rmult (/ INR (m + 1))) l). repeat split. rewrite map_length. apply H11.
      apply Forall_forall. intros x H14. rewrite Forall_forall in H12. apply in_map_iff in H14 as [x' [H14 H15]]. rewrite <- H14. apply H12 in H15. apply mult_rational; auto. exists (1%Z), (Z.of_nat (m + 1)). rewrite INR_IZR_INZ. lra.
      replace ((fun i : nat => nth i (map (Rmult (/ INR (m + 1))) l) 0 * INR n ^ (i + 1))) with (fun i : nat => (/ INR (m + 1)) * (nth i l 0) * INR n ^(i+1)).
      2 : { apply functional_extensionality. intros k. rewrite <- map_nth. rewrite Rmult_0_r. reflexivity. }
      rewrite H13. unfold Rdiv. rewrite Rmult_comm. rewrite r_mult_sum_f_i_n_f_l. apply sum_f_equiv; try lia. intros k H14. lra.
    }
    assert (H13 : exists l1 : list (list R), length l1 = m /\ Forall (fun l2 => length l2 = m /\ Forall rational l2 /\ (forall i : nat, nth i l1 [] = l2 -> choose (m + 1) (i+2) * sum_f 1 n (fun k : nat => INR k ^ (m + 1 - (i+2))) = sum_f 0 (m - 1) (fun i : nat => nth i l2 0 * INR n ^ (i + 1)) )) l1).
    { 
      pose proof (test_lemmos2 m n H3 H10) as H13. destruct H13 as [l1 H13]. exists l1. split. rewrite Forall_forall in H13.
      2 : { apply Forall_forall. intros x H14. repeat split. rewrite Forall_forall in H13. apply H13. auto.
            apply Forall_forall. intros i H15. rewrite Forall_forall in H13. destruct H13 as [H13 H16]. specialize (H16 x H14) as [H16 [H17 H18]]. rewrite Forall_forall in H17. specialize (H17 i H15). apply H17.
       intros i H15. rewrite Forall_forall in H13. destruct H13 as [H13 H16]. specialize (H16 x H14). apply H16. auto. }
      tauto.
    }
    assert (H14 : exists l1 : list R, length l1 = m /\ Forall rational l1 /\ sum_f 2 (m + 1) (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j))) = sum_f 0 (m - 1) (fun i : nat => nth i l1 0 * INR n ^ (i + 1))).
    { apply add_lists_sum_f; try lia. auto. }
    assert (H15 : exists l1 : list R, length l1 = m /\ Forall rational l1 /\ sum_f 2 (m + 1) (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j))) / INR (m + 1) = sum_f 0 (m - 1) (fun i : nat => nth i l1 0 * INR n ^ (i + 1))).
    {
      destruct H14 as [l1 [H14 [H15 H16]]]. exists (map (Rmult (/ INR (m + 1))) l1). repeat split. rewrite map_length. apply H14.
      apply Forall_forall. intros x H17. rewrite Forall_forall in H15. apply in_map_iff in H17 as [x' [H17 H18]]. rewrite <- H17. apply H15 in H18. apply mult_rational; auto. exists (1%Z), (Z.of_nat (m + 1)). rewrite INR_IZR_INZ. lra.
      replace ((fun i : nat => nth i (map (Rmult (/ INR (m + 1))) l1) 0 * INR n ^ (i + 1))) with (fun i : nat => (/ INR (m + 1)) * (nth i l1 0) * INR n ^(i+1)).
      2 : { apply functional_extensionality. intros k. rewrite <- map_nth. rewrite Rmult_0_r. reflexivity. }
      rewrite H16. unfold Rdiv. rewrite Rmult_comm. rewrite r_mult_sum_f_i_n_f_l. apply sum_f_equiv; try lia. intros k H17. lra.
    }
    assert (H16 : exists l1 : list R, length l1 = m /\ Forall rational l1 /\ - sum_f 2 (m + 1) (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j))) / INR (m + 1) = sum_f 0 (m - 1) (fun i : nat => nth i l1 0 * INR n ^ (i + 1))).
    {
      destruct H15 as [l1 [H15 [H16 H17]]]. exists (map (Rmult (-1)) l1). repeat split. rewrite map_length. apply H15.
      apply Forall_forall. intros x H18. rewrite Forall_forall in H16. apply in_map_iff in H18 as [x' [H18 H19]]. rewrite <- H18. apply H16 in H19. apply mult_rational; auto. exists (1%Z), ((-1)%Z). lra.
      replace ((fun i : nat => nth i (map (Rmult (-1)) l1) 0 * INR n ^ (i + 1))) with (fun i : nat => (-1) * (nth i l1 0) * INR n ^(i+1)).
      2 : { apply functional_extensionality. intros k. rewrite <- map_nth. rewrite Rmult_0_r. reflexivity. } 
      replace ((fun j : nat => -1 * choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j)))) with ((fun j : nat => -1 * (choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j))))).
      2 : { apply functional_extensionality. intros k. lra. } replace (- sum_f 2 (m + 1) (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j)))) with (-1 * sum_f 2 (m + 1) (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j)))) by nra.
      unfold Rdiv in *. rewrite Rmult_assoc. rewrite H17. replace ((fun i : nat => -1 * nth i l1 0 * INR n ^ (i + 1))) with ((fun i : nat => -1 * (nth i l1 0 * INR n ^ (i + 1)))).
      2 : { apply functional_extensionality. intros k. lra. } rewrite <- r_mult_sum_f_i_n_f_l. apply Rmult_eq_compat_l. apply sum_f_equiv; try lia. intros k H18. lra.
    }
    destruct H16 as [l1 [H16 [H17 H18]]]. destruct H12 as [l2 [H12 [H19 H20]]]. exists (add_lists l1 l2). repeat split. 
    3 : 
    {
      rewrite H20. unfold Rminus. replace (sum_f 0 (m - 1) (fun i : nat => nth i l2 0 * INR n ^ (i + 1)) + - (sum_f 2 (m + 1) (fun j : nat => choose (m + 1) j * sum_f 1 n (fun i : nat => INR i ^ (m + 1 - j))) / INR (m + 1))) with 
      (sum_f 0 (m - 1) (fun i : nat => nth i l2 0 * INR n ^ (i + 1)) + sum_f 0 (m - 1) (fun i : nat => nth i l1 0 * INR n ^ (i + 1))) by lra. 
      rewrite sum_f_plus; try lia. apply sum_f_equiv; try lia. intros k H21. rewrite <- Rmult_plus_distr_r. rewrite Rplus_comm. rewrite <- add_lists_separate with (k := k) (m := m); try lia. lra.
    }
    2 : { apply add_lists_rational; auto. }
    rewrite add_lists_length. rewrite H16. rewrite H12. lia. 
Qed.

Close Scope R_scope.

Open Scope Z_scope.

Lemma Z_ind_pos:
  forall (P: Z -> Prop),
  P 0 ->
  (forall z, z >= 0 -> P z -> P (z + 1)) ->
  forall z, z >= 0 -> P z.
Proof.
  intros P H0 Hstep z Hnonneg.

  (* Convert the problem to induction over natural numbers *)
  remember (Z.to_nat z) as n eqn:Heq.
  assert (Hnneg: forall n : nat, P (Z.of_nat n)).
  {
    intros n1. induction n1.
    - simpl. apply H0.
    - replace (S n1) with (n1 + 1)%nat by lia.
      rewrite Nat2Z.inj_add. apply Hstep. lia. apply IHn1.
  }

  specialize(Hnneg n). rewrite Heq in Hnneg.
  replace (Z.of_nat (Z.to_nat z)) with (z) in Hnneg. apply Hnneg.
  rewrite Z2Nat.id. lia. lia.
Qed.

Lemma Z_induction_bidirectional :
  forall P : Z -> Prop,
  P 0 ->
  (forall n : Z, P n -> P (n + 1)) ->
  (forall n : Z, P n -> P (n - 1)) ->
  forall n : Z, P n.
Proof.
  intros P H0 Hpos Hneg n.

  assert (Hnneg: forall n : nat, P (Z.of_nat n)).
  {
    intros n1. induction n1.
    - simpl. apply H0.
    - replace (S n1) with (n1 + 1)%nat by lia.
      rewrite Nat2Z.inj_add. apply Hpos. apply IHn1.
  }

  destruct (Z_lt_le_dec n 0).
  - replace n with (- Z.of_nat (Z.to_nat (- n))) by
      (rewrite Z2Nat.id; lia).
    induction (Z.to_nat (-n)).
    + simpl. apply H0.
    + replace (S n0) with (n0 + 1)%nat by lia. rewrite Nat2Z.inj_add.
      replace (- (Z.of_nat n0 + Z.of_nat 1)) with (-Z.of_nat n0 - 1) by lia. apply Hneg. apply IHn0.
  - apply Z_ind_pos.
    -- apply H0.
    -- intros z H. apply Hpos.
    -- lia.
Qed.

Lemma strong_induction_Z :
  forall P : Z -> Prop,
  (forall m, (forall k : Z, 0 <= k < m -> P k) -> P m) ->
  forall n, 0 <= n -> P n.
Proof.
  intros P H1 n H2. assert (H3: forall k, 0 <= k < n -> P k).
  - apply Z_induction_bidirectional with (n := n).
    -- lia.
    -- intros z H. intros k Hk. apply H1. intros k' Hk'. apply H. lia.
    -- intros z H. intros k Hk. apply H1. intros k' Hk'. apply H. lia.
  - apply H1. intros k Hk. apply H3. lia.
Qed.

Lemma well_ordering_principle_contrapositive_Z : forall E : Z -> Prop,
  (forall n : Z, E n -> n >= 0) ->
  (~(exists m, E m /\ forall k, k >= 0 -> E k -> m <= k)) ->
    (~(exists n, E n)).
Proof.
  intros E Hnon_neg H.
  set (E' := fun z => ~ E z).
  assert (E 0 -> False).
  { intros H2. apply H. exists 0. split; try split.
    - apply H2.
    - intros k _ H3. specialize (Hnon_neg k). apply Hnon_neg in H3. lia.
  }
  assert (H2: forall z, z >= 0 -> E' z).
  {
    intros z Hz. apply strong_induction_Z. intros m H2. destruct (Z_le_dec m 0).
    - unfold E'. unfold not. apply Z_le_lt_eq_dec in l. destruct l.
      -- specialize (Hnon_neg m). intros H3. apply Hnon_neg in H3. lia.
      -- rewrite e. apply H0.
    - assert (E m -> False).
      { intros H3. apply H. exists m. split; try split.
        - apply H3.
        - intros k H4 H5. specialize (H2 k). assert (E' k -> False). unfold E'.
          unfold not. intros H6. apply H6. apply H5. assert (0 <= k < m -> False) by auto.
          lia.
      }
      unfold E'. unfold not. apply H1.
    - lia.
  }
  unfold E' in H2. unfold not in H2. unfold not. intros H3. destruct H3 as [n H3].
  specialize (H2 n). apply H2. apply Hnon_neg in H3. apply H3. apply H3.
Qed.

Theorem well_ordering_Z : forall E : Z -> Prop,
  (forall z, E z -> z >= 0) ->
  (exists x, E x) ->
  (exists n, E n /\ forall m, m >= 0 -> E m -> (n <= m)).
Proof.
  intros E Hnon_neg [x Ex].
  assert (H :
    (forall n : Z, E n -> n >= 0) ->
      (~(exists m, E m /\ forall k, k >= 0 -> E k -> m <= k)) ->
      (~(exists n, E n))).
    { apply well_ordering_principle_contrapositive_Z. }

  destruct (classic (exists m, E m /\ forall k, k >= 0 -> E k -> m <= k)) as [C1|C2].
  - apply C1.
  - exfalso. apply H in C2. apply C2. exists x. apply Ex. apply Hnon_neg.
Qed.

Theorem QRTE : forall a d : Z,
  (d >= 1) -> exists q r : Z, a = d * q + r /\ 0 <= r < d.
Proof.
  intros a d Hb.
  set (S z := exists t : Z, z = a - t * d /\ z >= 0).
  assert (Ht : exists t : Z, S t).
  {
    destruct (Z_le_dec 0 a) as [Ha | Ha].
    - exists a. unfold S. exists 0. split. simpl. rewrite Z.sub_0_r. reflexivity. apply Z.le_ge. apply Ha.
    - unfold not in Ha. exists (a * (1 - d)). unfold S. exists a. split. lia.
      assert (1 - d <= 0) by lia. destruct (Z.eq_dec (1 - d) 0) as [H2 | H2].
      -- lia.
      -- assert (H3 : 1 - d < 0) by lia. assert (H4 : a < 0) by lia.
         assert (H5 : forall z : Z, z > 0 -> z >= 0) by lia. apply H5.
         apply Z.lt_gt. apply Z.mul_neg_neg. lia. lia.
  }
  apply well_ordering_Z in Ht.
  - destruct Ht as [r Ht]. destruct Ht as [Ht Ht'].
    unfold S in Ht. destruct Ht as [t Ht]. destruct Ht as [Ht Ht''].
    exists t. exists r. split. lia. destruct (classic (r < d)) as [H1 | H1].
    -- lia.
    -- assert (H2 : r >= d) by lia. assert (H3 : a - t * d >= d) by lia.
       assert (H4 : a - d * (t - 1) >= 0) by lia.  assert (H5 : r - d >= 0) by lia.
       assert (H6 : S (r - d)). { unfold S. exists (t + 1). split. lia. lia. }
       assert (H7 : S (a - d * (t + 1))). { unfold S. exists (t + 1). split. lia. lia. }
       assert (H8 : r <= r - d). { apply Ht'. lia. apply H6. } lia.
    - intros z. unfold S. intros H. destruct H as [t H]. lia.
Qed.

Theorem QRTU : forall a d q1 q2 r1 r2 : Z,
  (d >= 1) /\  a = d * q1 + r1 /\ a = d * q2 + r2 /\ 0 <= r1 < d /\ 0 <= r2 < d
  -> q1 = q2 /\ r1 = r2.
Proof.
  intros a d q1 q2 r1 r2 [H1 [H2 [H3 [H4 H5]]]].
  assert (H: q1 = q2).
  {
    assert (H6 : q1 * d + r1 = q2 * d + r2) by lia.
    assert (H7 : (q1 - q2) * d = r2 - r1) by lia.
    assert (H8 : -d < -r1 <= 0) by lia.
    assert (H9 : 0 <= r2 < d) by lia.
    assert (H10 : -d < r2 - r1 < d) by lia.
    assert (H11 : -d < (q1 - q2) * d < d) by lia.
    destruct H11 as [H11 H12].
    assert (H13 : -1 < q1 - q2).
    { apply Zmult_lt_reg_r with (p := d). lia. lia. }
    assert (H14 : q1 - q2 < 1).
    { apply Zmult_lt_reg_r with (p := d). lia. lia. }
    lia.
  }
  split.
  - apply H.
  - lia.
Qed.

Theorem QRT : forall a d : Z,
  d >= 1 ->
  exists! p : (Z * Z), let (q, r) := p in a = d * q + r /\ 0 <= r < d.
Proof.
  intros a d Hd.
  apply unique_existence with (P := fun p : (Z * Z) => let (q, r) := p in a = d * q + r /\ 0 <= r < d).
  split.
  - destruct (QRTE a d Hd) as [q [r [H1 H2]]].
    exists (q, r). auto.
  - intros [q1 r1] [q2 r2] [H1a H1b] [H2a H2b].
    assert (H3 : q1 = q2 /\ r1 = r2) by (apply QRTU with (a := a) (d := d); auto).
    destruct H3 as [H3a H3b]. rewrite H3a. rewrite H3b. reflexivity.
Qed.

Lemma gcd_0 : forall a b : Z, Z.gcd a b = 0 -> a = 0 /\ b = 0.
Proof.
  intros a b H1. split.
  - pose proof Z.gcd_divide_l a b as H2. destruct H2 as [k H2]. lia.
  - pose proof Z.gcd_divide_r a b as H2. destruct H2 as [k H2]. lia.
Qed.

Lemma gcd_gt_0 : forall a b : Z, a <> 0 -> b <> 0 -> Z.gcd a b > 0.
Proof.
  intros a b H1 H2. pose proof Z.gcd_nonneg a b. assert (Z.gcd a b = 0 \/ Z.gcd a b > 0) as [H3 | H3] by lia.
  - apply gcd_0 in H3. lia.
  - auto.
Qed.

Lemma rational_representation : forall r z1 z2,
  z1 <> 0 -> z2 <> 0 ->
  (r = IZR z1 / IZR z2)%R -> exists z1' z2',
    ((r = IZR z1' / IZR z2')%R /\ (forall x, x > 1 -> ~(x | z1') \/ ~(x | z2'))).
Proof.
  intros r z1 z2 H1 H2 H3. exists (z1 / Z.gcd z1 z2). exists (z2 / Z.gcd z1 z2). split.
  - rewrite H3. pose proof Z.gcd_divide_r z1 z2 as H4. pose proof Z.gcd_divide_l z1 z2 as H5.
    unfold Z.divide in H4. unfold Z.divide in H5. destruct H4 as [k1 H4]. destruct H5 as [k2 H5].
    assert (Z.gcd z1 z2 <> 0) as H6 by lia.
    assert (H7 : Z.gcd z1 z2 > 0). { pose proof Z.gcd_nonneg z1 z2. lia. }
    replace (z1 / Z.gcd z1 z2) with (k2). 2 : { rewrite H5 at 1. rewrite Z_div_mult. reflexivity. lia. }
    replace (z2 / Z.gcd z1 z2) with (k1). 2 : { rewrite H4 at 1. rewrite Z_div_mult. reflexivity. lia. }
    rewrite H4. rewrite H5 at 1. repeat rewrite mult_IZR.
    replace ((IZR k2 * IZR (Z.gcd z1 z2) / (IZR k1 * IZR (Z.gcd z1 z2)))%R) with
            ( IZR k2 / IZR k1 * (IZR (Z.gcd z1 z2) / IZR (Z.gcd z1 z2)))%R.
    2 : { field. split. apply not_0_IZR. auto. apply not_0_IZR. lia. }
    rewrite Rdiv_diag. 2 : { apply not_0_IZR. lia. } nra.
  - intros x H4. apply not_and_or. intros [[a H5] [b H6]]. pose proof Z.gcd_divide_l z1 z2 as [c H7].
    pose proof Z.gcd_divide_r z1 z2 as [d H8]. rewrite H7 in H5 at 1. rewrite H8 in H6 at 1.
    rewrite Z_div_mult in H5 by (apply gcd_gt_0; auto). rewrite Z_div_mult in H6 by (apply gcd_gt_0; auto).
    rewrite H5 in H7. rewrite H6 in H8. assert (H9 : Z.divide (x * Z.gcd z1 z2) z1). { rewrite H7 at 2. exists (a). lia. }
    assert (H10 : Z.divide (x * Z.gcd z1 z2) z2). { exists (b). lia. } pose proof Z.gcd_greatest z1 z2 (x * Z.gcd z1 z2) as H11.
    apply H11 in H9. 2 : { auto. } unfold Z.divide in H9. destruct H9 as [k H9]. assert (Z.gcd z1 z2 > 0) as H12 by (apply gcd_gt_0; auto).
    assert (k < 0 \/ k = 0 \/ k > 0) as [H13 | [H13 | H13]] by lia.
    -- nia.
    -- nia.
    -- assert (H14 : k * x * Z.gcd z1 z2 > Z.gcd z1 z2). { rewrite <- Zmult_1_l. apply Zmult_gt_compat_r. lia. lia. }
       nia.
Qed.

Lemma even_pow2 : forall z,
  Z.Even (z * z) -> Z.Even z.
Proof.
  intros z H. pose proof lemma_2_8' z as [H1 | H1].
  - auto.
  - destruct H1 as [k H1]. destruct H as [k' H]. nia.
Qed.

Lemma sqrt_rational_neq_0 : forall r z1 z2,
  (r > 0)%R -> sqrt r = (IZR z1 / IZR z2)%R -> (z1 <> 0 /\ z2 <> 0).
Proof.
  intros r z1 z2 H1 H2. split.
  - intros H3. rewrite H3 in H2. rewrite Rdiv_0_l in H2. pose proof sqrt_lt_R0 r. nra.
  - intros H3. rewrite H3 in H2. rewrite Rdiv_0_r in H2. pose proof sqrt_lt_R0 r. nra.
Qed.

Lemma sqrt_2_irrational : irrational (sqrt 2).
Proof.
  unfold irrational. unfold rational. unfold not. intros [z1 [z2 H1]].
  assert (z1 <> 0 /\ z2 <> 0) as [H2 H3] by (apply sqrt_rational_neq_0 with (r := 2%R); lra).
  assert (H4 : exists z1' z2', ((sqrt 2 = IZR z1' / IZR z2')%R /\ (forall x, x > 1 -> ~(x | z1') \/ ~(x | z2')))).
  { apply rational_representation with (z1 := z1) (z2 := z2). apply H2. apply H3. apply H1. }
  destruct H4 as [z1' [z2' [H4 H5]]]. assert (H6 : (sqrt 2 * sqrt 2 = (IZR z1' / IZR z2') * (IZR z1' / IZR z2'))%R) by nra.
  rewrite sqrt_sqrt in H6. 2 : { lra. } assert (H7 : (z1' <> 0 /\ z2' <> 0)) by (apply sqrt_rational_neq_0 with (r := 2%R); lra).
  destruct H7 as [H7 H8]. assert (H9 : (IZR z1' <> 0)%R) by (apply not_0_IZR; auto). assert (H10 : (IZR z2' <> 0)%R) by (apply not_0_IZR; auto).
  replace (IZR z1' / IZR z2' * (IZR z1' / IZR z2'))%R with ((IZR z1')^2 / (IZR z2')^2)%R in H6.
  2 : { field. auto. } apply Rmult_eq_compat_r with (r := ((IZR z2')^2)%R) in H6.
  replace ((IZR z1' ^ 2 / IZR z2' ^ 2 * IZR z2' ^ 2)%R) with ((IZR z1')^2)%R in H6.
  2 : { field. auto. } simpl in H6. repeat rewrite Rmult_1_r in H6. repeat rewrite <- mult_IZR in H6.
  apply eq_IZR in H6. assert (H11 : Z.Even (z1' * z1')). { exists (z2' * z2'). lia. }
  apply even_pow2 in H11. destruct H11 as [k1 H11]. assert (H12 : Z.Even (z2' * z2')). { exists (k1 * k1). nia. }
  apply even_pow2 in H12. destruct H12 as [k2 H12]. specialize (H5 2). destruct H5 as [H5 | H5].
  { lia. } { apply H5. unfold Z.divide. exists (k1). lia. } { apply H5. unfold Z.divide. exists (k2). lia. }
Qed.

Lemma lemma_2_12_a' : forall a,
  irrational a -> exists b, irrational b /\ rational (a + b).
Proof.
  intros a H1. exists (-a)%R. split.
  - intros [z1 [z2 H2]]. apply H1. exists (-z1), z2. replace (-z1) with (-1 * z1) by lia. rewrite mult_IZR. lra.
  - exists 0, 1. nra.
Qed.

Lemma lemma_2_12_b : forall b,
  irrational b -> exists a, rational a /\ rational (a * b).
Proof.
  intros a H1. exists 0%R. split; exists 0, 1; nra.
Qed.

Lemma lemma_2_12_b' : forall a b,
  a <> 0%R -> rational a -> irrational b -> irrational (a * b).
Proof.
  intros a b H1 H2 H3. assert (irrational (a * b) \/ rational (a * b)) as [H4 | H4].
  { unfold irrational. tauto. } auto.
  destruct H2 as [z1 [z2 H2]]. assert (H5 : z1 <> 0). { apply x_neq_0_IZR_num_neq_0 with (x := a) (y := z1) (z := z2). auto. }
  assert (H6 : z2 <> 0). { apply x_neq_0_IZR_den_neq_0 with (x := a) (y := z1) (z := z2). auto. }
  assert (H7 : rational (/ a)) by (exists z2, z1; rewrite H2; field; split; apply not_0_IZR; lia).
  assert (H8 : b <> 0%R) by (intros H8; apply H3; exists 0, 1; nra).
  assert (H9 : (/ a <> 0)%R) by (apply Rinv_neq_0_compat; auto).
  assert (H10 : rational b).
  { replace b with (a * b / a)%R by (field; auto). apply mult_rational; auto. }
  unfold irrational in H3. tauto.
Qed.

Lemma lemma_2_12_a'' : exists a b, irrational (a + b).
Proof.
  exists (sqrt 2), (sqrt 2). replace (sqrt 2 + sqrt 2)%R with (2 * sqrt 2)%R by lra. apply lemma_2_12_b' with (a := 2%R) (b := (sqrt 2)%R).
  - lra.
  - exists 2, 1. nra.
  - apply sqrt_2_irrational.
Qed.

Lemma lemma_2_12_c : exists a,
  irrational (a^2) /\ rational (a^4).
Proof.
  exists (sqrt (sqrt 2)). split.
  - simpl. rewrite Rmult_1_r. rewrite sqrt_sqrt. 2 : { apply Rlt_le. apply sqrt_lt_R0. lra. } apply sqrt_2_irrational.
  - exists 2, 1. simpl. rewrite Rmult_1_r. rewrite sqrt_sqrt. 2 : { apply Rlt_le. apply sqrt_lt_R0. lra. }
    rewrite <- Rmult_assoc. rewrite sqrt_sqrt. 2 : { apply Rlt_le. apply sqrt_lt_R0. lra. } 
    rewrite sqrt_sqrt; nra.
Qed.

Lemma lemma_2_12_d : exists a b,
  irrational a -> irrational b -> rational (a * b) /\ rational (a + b).
Proof.
  exists (sqrt 2), (-(sqrt 2))%R. intros H1 H2. split.
  - exists (-2), 1. replace (sqrt 2 * - sqrt 2)%R with (- (sqrt 2 * sqrt 2))%R by lra. rewrite sqrt_sqrt; lra.
  - exists 0, 1. lra.
Qed.

Ltac zforms :=
  match goal with
  | [ |- exists _, ?n = ?num * _ \/ _ ] =>
      destruct (QRTE n num) as [q [r Hqr]];
      try exists q;
      lia
  | _ => fail "Goal does not match expected pattern"
  end.

Lemma ksqr_div_3_k_div_3 : forall k,
  Z.divide 3 (k^2) -> Z.divide 3 k.
Proof.
  intros k [a H1]. unfold Z.divide.
  assert (exists p, k = 3*p \/ k = 3*p+1 \/ k = 3*p+2) as [p H2] by zforms.
  exists p. lia.
Qed.

Lemma lemma_2_13_a : irrational (sqrt 3).
Proof.
  unfold irrational. unfold rational. unfold not. intros [z1 [z2 H1]].
  assert (z1 <> 0 /\ z2 <> 0) as [H2 H3] by (apply sqrt_rational_neq_0 with (r := 3%R); lra).
  assert (H4 : exists z1' z2', ((sqrt 3 = IZR z1' / IZR z2')%R /\ (forall x, x > 1 -> ~(x | z1') \/ ~(x | z2')))).
  { apply rational_representation with (z1 := z1) (z2 := z2). apply H2. apply H3. apply H1. }
  destruct H4 as [z1' [z2' [H4 H5]]]. assert (H6 : (sqrt 3 * sqrt 3 = (IZR z1' / IZR z2') * (IZR z1' / IZR z2'))%R) by nra.
  rewrite sqrt_sqrt in H6. 2 : { lra. } assert (H7 : (z1' <> 0 /\ z2' <> 0)) by (apply sqrt_rational_neq_0 with (r := 3%R); lra).
  destruct H7 as [H7 H8]. assert (H9 : (IZR z1' <> 0)%R) by (apply not_0_IZR; auto). assert (H10 : (IZR z2' <> 0)%R) by (apply not_0_IZR; auto).
  replace (IZR z1' / IZR z2' * (IZR z1' / IZR z2'))%R with ((IZR z1')^2 / (IZR z2')^2)%R in H6.
  2 : { field. auto. } apply Rmult_eq_compat_r with (r := ((IZR z2')^2)%R) in H6.
  replace ((IZR z1' ^ 2 / IZR z2' ^ 2 * IZR z2' ^ 2)%R) with ((IZR z1')^2)%R in H6.
  2 : { field. auto. } simpl in H6. repeat rewrite Rmult_1_r in H6. repeat rewrite <- mult_IZR in H6. apply eq_IZR in H6.
  assert (Z.divide 3 (z1'^2)) as H11 by (exists (z2' * z2'); lia). assert (Z.divide 3 z1') as H12 by (apply ksqr_div_3_k_div_3; auto).
  pose proof H11 as [p H13]. pose proof H12 as [q H14]. replace (z1'^2) with (z1' * z1') in H13 by lia.
  assert (H15 : z1' * z1' = 3 * (3 * q * q)) by lia. rewrite H15 in H6. assert (Z.divide 3 (z2'^2)) as H16 by (exists (q * q); lia).
  assert (Z.divide 3 z2') as H17 by (apply ksqr_div_3_k_div_3; auto). specialize (H5 3). destruct H5 as [H5 | H5].
  { lia. } { tauto. } { tauto. }
Qed.

Lemma ksqr_div_3_k_div_5 : forall k,
  Z.divide 5 (k^2) -> Z.divide 5 k.
Proof.
  intros k [a H1]. unfold Z.divide.
  assert (exists p, k = 5*p \/ k = 5*p+1 \/ k = 5*p+2 \/ k = 5*p+3 \/ k = 5*p+4) as [p H2] by zforms.
  exists p. lia.
Qed.

Lemma lemma_2_13_a' : irrational (sqrt 5).
Proof.
  unfold irrational. unfold rational. unfold not. intros [z1 [z2 H1]].
  assert (z1 <> 0 /\ z2 <> 0) as [H2 H3] by (apply sqrt_rational_neq_0 with (r := 5%R); lra).
  assert (H4 : exists z1' z2', ((sqrt 5 = IZR z1' / IZR z2')%R /\ (forall x, x > 1 -> ~(x | z1') \/ ~(x | z2')))).
  { apply rational_representation with (z1 := z1) (z2 := z2). apply H2. apply H3. apply H1. }
  destruct H4 as [z1' [z2' [H4 H5]]]. assert (H6 : (sqrt 5 * sqrt 5 = (IZR z1' / IZR z2') * (IZR z1' / IZR z2'))%R) by nra.
  rewrite sqrt_sqrt in H6. 2 : { lra. } assert (H7 : (z1' <> 0 /\ z2' <> 0)) by (apply sqrt_rational_neq_0 with (r := 5%R); lra).
  destruct H7 as [H7 H8]. assert (H9 : (IZR z1' <> 0)%R) by (apply not_0_IZR; auto). assert (H10 : (IZR z2' <> 0)%R) by (apply not_0_IZR; auto).
  replace (IZR z1' / IZR z2' * (IZR z1' / IZR z2'))%R with ((IZR z1')^2 / (IZR z2')^2)%R in H6.
  2 : { field. auto. } apply Rmult_eq_compat_r with (r := ((IZR z2')^2)%R) in H6.
  replace ((IZR z1' ^ 2 / IZR z2' ^ 2 * IZR z2' ^ 2)%R) with ((IZR z1')^2)%R in H6.
  2 : { field. auto. } simpl in H6. repeat rewrite Rmult_1_r in H6. repeat rewrite <- mult_IZR in H6. apply eq_IZR in H6.
  assert (Z.divide 5 (z1'^2)) as H11 by (exists (z2' * z2'); lia). assert (Z.divide 5 z1') as H12 by (apply ksqr_div_3_k_div_5; auto).
  pose proof H11 as [p H13]. pose proof H12 as [q H14]. replace (z1'^2) with (z1' * z1') in H13 by lia.
  assert (H15 : z1' * z1' = 5 * (5 * q * q)) by lia. rewrite H15 in H6. assert (Z.divide 5 (z2'^2)) as H16 by (exists (q * q); lia).
  assert (Z.divide 5 z2') as H17 by (apply ksqr_div_3_k_div_5; auto). specialize (H5 5). destruct H5 as [H5 | H5].
  { lia. } { tauto. } { tauto. }
Qed.

Lemma ksqr_div_6_k_div_6 : forall k,
  Z.divide 6 (k^2) -> Z.divide 6 k.
Proof.
  intros k [a H1]; unfold Z.divide;
  assert (exists p, k=6*p\/k=6*p+1\/k=6*p+2\/k=6*p+3\/k=6*p+4\/k=6*p+5) as [p H2] by zforms;
  exists p; lia.
Qed.

Lemma lemma_2_13_a'' : irrational (sqrt 6).
Proof.
  unfold irrational. unfold rational. unfold not. intros [z1 [z2 H1]].
  assert (z1 <> 0 /\ z2 <> 0) as [H2 H3] by (apply sqrt_rational_neq_0 with (r := 6%R); lra).
  assert (H4 : exists z1' z2', ((sqrt 6 = IZR z1' / IZR z2')%R /\ (forall x, x > 1 -> ~(x | z1') \/ ~(x | z2')))).
  { apply rational_representation with (z1 := z1) (z2 := z2). apply H2. apply H3. apply H1. }
  destruct H4 as [z1' [z2' [H4 H5]]]. assert (H6 : (sqrt 6 * sqrt 6 = (IZR z1' / IZR z2') * (IZR z1' / IZR z2'))%R) by nra.
  rewrite sqrt_sqrt in H6. 2 : { lra. } assert (H7 : (z1' <> 0 /\ z2' <> 0)) by (apply sqrt_rational_neq_0 with (r := 6%R); lra).
  destruct H7 as [H7 H8]. assert (H9 : (IZR z1' <> 0)%R) by (apply not_0_IZR; auto). assert (H10 : (IZR z2' <> 0)%R) by (apply not_0_IZR; auto).
  replace (IZR z1' / IZR z2' * (IZR z1' / IZR z2'))%R with ((IZR z1')^2 / (IZR z2')^2)%R in H6.
  2 : { field. auto. } apply Rmult_eq_compat_r with (r := ((IZR z2')^2)%R) in H6.
  replace ((IZR z1' ^ 2 / IZR z2' ^ 2 * IZR z2' ^ 2)%R) with ((IZR z1')^2)%R in H6.
  2 : { field. auto. } simpl in H6. repeat rewrite Rmult_1_r in H6. repeat rewrite <- mult_IZR in H6. apply eq_IZR in H6.
  assert (Z.divide 6 (z1'^2)) as H11 by (exists (z2' * z2'); lia). assert (Z.divide 6 z1') as H12 by (apply ksqr_div_6_k_div_6; auto).
  pose proof H11 as [p H13]. pose proof H12 as [q H14]. replace (z1'^2) with (z1' * z1') in H13 by lia.
  assert (H15 : z1' * z1' = 6 * (6 * q * q)) by lia. rewrite H15 in H6. assert (Z.divide 6 (z2'^2)) as H16 by (exists (q * q); lia).
  assert (Z.divide 6 z2') as H17 by (apply ksqr_div_6_k_div_6; auto). specialize (H5 6). destruct H5 as [H5 | H5].
  { lia. } { tauto. } { tauto. }
Qed.

Lemma kcub_even_k_even : forall k,
  Z.Even (k^3) -> Z.Even k.
Proof.
  intros k H1. pose proof lemma_2_8' k as [H2 | H2].
  - auto.
  - destruct H2 as [k' H2]. assert (Z.Odd (k^3)) as H3.
    { exists (4*k'^3 + 6*k'^2 + 3*k'). nia. } rewrite <- Zodd_equiv in H3.
    rewrite <- Zeven_equiv in H1. apply Zodd_not_Zeven in H3. tauto.
Qed.

Lemma lemma_2_13_b : irrational (Rpower 2 (1/3)).
Proof.
  unfold irrational. unfold rational. unfold not. intros [z1 [z2 H1]].
  assert (H2 : Rpower 2 (1/3) <> 0%R). 
  { assert (H3 : (Rpower 2 0 < Rpower 2 (1/3))%R) by (apply Rpower_lt; lra). rewrite Rpower_O in H3; lra. }
  assert (z1 <> 0 /\ z2 <> 0) as [H3 H4].
  { assert (z1 = 0 \/ z2 = 0 \/ z1 <> 0 /\ z2 <> 0) as [H3 | [H3 | H3]] by lia; auto; rewrite H3 in H1; try rewrite Rdiv_0_l in H1; try rewrite Rdiv_0_r in H1; lra. }
  assert (H5 : exists z1' z2', ((Rpower 2 (1/3) = IZR z1' / IZR z2')%R /\ (forall x, x > 1 -> ~(x | z1') \/ ~(x | z2')))).
  { apply rational_representation with (z1 := z1) (z2 := z2). apply H3. apply H4. apply H1. }
  destruct H5 as [z1' [z2' [H5 H6]]]. assert (H7 : (Rpower 2 (1/3) * Rpower 2 (1/3) * Rpower 2 (1/3) = (IZR z1' / IZR z2') * (IZR z1' / IZR z2') * (IZR z1' / IZR z2'))%R) by nra.
  assert (H8 : z1' <> 0 /\ z2' <> 0).
  { assert (z1' = 0 \/ z2' = 0 \/ z1' <> 0 /\ z2' <> 0) as [H8 | [H8 | H8]] by lia; auto; rewrite H8 in H5; try rewrite Rdiv_0_l in H5; try rewrite Rdiv_0_r in H5; lra. }
  replace (Rpower 2 (1/3) * Rpower 2 (1/3) * Rpower 2 (1/3))%R with 2%R in H7.
  2 : { repeat rewrite <- Rpower_plus. replace (1/3 + 1/3 + 1/3)%R with 1%R by lra. rewrite Rpower_1;lra. }
  replace (IZR z1' / IZR z2' * (IZR z1' / IZR z2') * (IZR z1' / IZR z2'))%R with ((IZR z1')^3 / (IZR z2')^3)%R in H7 by (field; apply not_0_IZR; tauto).
    apply Rmult_eq_compat_r with (r := ((IZR z2')^3)%R) in H7. replace ((IZR z1' ^ 3 / IZR z2' ^ 3 * IZR z2' ^ 3)%R) with ((IZR z1')^3)%R in H7 by (field; apply not_0_IZR; tauto).
  replace 3 % nat with (Z.to_nat 3) in H7 at 1 by auto.
  assert (Z.Even (z1'^3)) as H9. 
  { replace 3 with (Z.of_nat 3) by auto. exists (z2'^3). apply eq_IZR. rewrite <- pow_IZR. rewrite mult_IZR. 
    apply eq_sym. rewrite pow_IZR in H7. replace (Z.of_nat (Z.to_nat 3)) with (3) in H7 by lia. apply H7. }
  assert (H10 : Z.Even z1'). { apply kcub_even_k_even in H9. auto. }
  assert (H11 : (2 | z1')). { destruct H10 as [k H10]. exists (k). lia. }
  destruct H10 as [k H10]. rewrite H10 in H7. assert (H12 : (IZR z2' ^ 3 = 4 * IZR (k^3))%R).
  { replace 3%nat with (Z.to_nat 3) in H7 by auto. rewrite pow_IZR with (z := 2 * k) in H7. replace (Z.to_nat 3) with 3%nat in H7 by auto.
    replace (Z.of_nat 3) with 3 in H7 by auto. replace ((2 * k) ^ 3) with (8 * k^3) in H7 by lia. rewrite mult_IZR in H7. nra. }
  assert (Z.Even (z2'^3)) as H13. 
  { replace 3 with (Z.of_nat 3) by auto. exists (2 * k^3). apply eq_IZR. rewrite <- pow_IZR. rewrite mult_IZR. 
    rewrite mult_IZR. replace (2 * (2 * IZR (k^3)))%R with (4 * IZR (k^3))%R by lra. nra. }
  assert (H14 : Z.Even z2'). { apply kcub_even_k_even in H13. auto. }
  assert (H15 : (2 | z2')). { destruct H14 as [k' H14]. exists (k'). lia. }
  specialize (H6 2) as [H6 | H6]; try lia; tauto.
Qed.

Lemma kcub_div_3_k_div_3 : forall k,
  Z.divide 3 (k^3) -> Z.divide 3 k.
Proof.
  intros k [a H1]. unfold Z.divide.
  assert (exists p, k = 3*p \/ k = 3*p+1 \/ k = 3*p+2) as [p H2] by zforms.
  exists p. lia.
Qed.

Lemma lemma_2_13_b' : irrational (Rpower 3 (1/3)).
Proof.
  unfold irrational. unfold rational. unfold not. intros [z1 [z2 H1]].
  assert (H2 : Rpower 3 (1/3) <> 0%R). 
  { assert (H3 : (Rpower 3 0 < Rpower 3 (1/3))%R) by (apply Rpower_lt; lra). rewrite Rpower_O in H3; lra. }
  assert (z1 <> 0 /\ z2 <> 0) as [H3 H4].
  { assert (z1 = 0 \/ z2 = 0 \/ z1 <> 0 /\ z2 <> 0) as [H3 | [H3 | H3]] by lia; auto; rewrite H3 in H1; try rewrite Rdiv_0_l in H1; try rewrite Rdiv_0_r in H1; lra. }
  assert (H5 : exists z1' z2', ((Rpower 3 (1/3) = IZR z1' / IZR z2')%R /\ (forall x, x > 1 -> ~(x | z1') \/ ~(x | z2')))).
  { apply rational_representation with (z1 := z1) (z2 := z2). apply H3. apply H4. apply H1. }
  destruct H5 as [z1' [z2' [H5 H6]]]. assert (H7 : (Rpower 3 (1/3) * Rpower 3 (1/3) * Rpower 3 (1/3) = (IZR z1' / IZR z2') * (IZR z1' / IZR z2') * (IZR z1' / IZR z2'))%R) by nra.
  assert (H8 : z1' <> 0 /\ z2' <> 0).
  { assert (z1' = 0 \/ z2' = 0 \/ z1' <> 0 /\ z2' <> 0) as [H8 | [H8 | H8]] by lia; auto; rewrite H8 in H5; try rewrite Rdiv_0_l in H5; try rewrite Rdiv_0_r in H5; lra. }
  replace (Rpower 3 (1/ 3) * Rpower 3 (1/3) * Rpower 3 (1/3))%R with 3%R in H7. 
  2 : { repeat rewrite <- Rpower_plus. replace (1/3 + 1/3 + 1/3)%R with 1%R by lra. rewrite Rpower_1;lra. }
  replace (IZR z1' / IZR z2' * (IZR z1' / IZR z2') * (IZR z1' / IZR z2'))%R with ((IZR z1')^3 / (IZR z2')^3)%R in H7 by (field; apply not_0_IZR; tauto).
    apply Rmult_eq_compat_r with (r := ((IZR z2')^3)%R) in H7. replace ((IZR z1' ^ 3 / IZR z2' ^ 3 * IZR z2' ^ 3)%R) with ((IZR z1')^3)%R in H7 by (field; apply not_0_IZR; tauto).
  replace 3 % nat with (Z.to_nat 3) in H7 at 1 by auto. assert (3 | z1'^3) as H9.
  { replace 3 with (Z.of_nat 3) by auto. exists (z2'^3). apply eq_IZR. rewrite <- pow_IZR. rewrite mult_IZR.
    apply eq_sym. rewrite pow_IZR in H7. simpl in *. nra. }
  assert (H10 : Z.divide 3 z1'). { apply kcub_div_3_k_div_3 in H9. auto. }
  destruct H10 as [k H10]. rewrite H10 in H7. assert (H11 : (IZR z2' ^ 3 = 9 * IZR (k^3))%R).
  { replace 3%nat with (Z.to_nat 3) in H7 by auto. rewrite pow_IZR with (z := k * 3) in H7. replace (Z.to_nat 3) with 3%nat in H7 by auto.
    replace (Z.of_nat 3) with 3 in H7 by auto. replace ((k * 3) ^ 3) with (27 * k^3) in H7 by lia. rewrite mult_IZR in H7. nra. }
  assert (Z.divide 3 (z2'^3)) as H12. { replace 3 with (Z.of_nat 3) by auto. exists (3 * k^3). apply eq_IZR. rewrite <- pow_IZR. rewrite mult_IZR. 
    rewrite mult_IZR. replace (IZR (Z.of_nat 3)) with 3%R by auto. nra. }
  assert (H13 : Z.divide 3 z2'). { apply kcub_div_3_k_div_3 in H12. auto. }
  assert (H14 : (3 | z1')). { exists (k). lia. }
  specialize (H6 3) as [H6 | H6]; try lia; tauto.
Qed.

Lemma rational_plus_rev : forall a b,
  rational (a + b) -> rational a -> rational b.
Proof.
  intros a b H1 H2. unfold rational in *. destruct H1 as [z1 [z2 H1]]. destruct H2 as [z3 [z4 H2]].
  assert (a = 0 /\ b = 0 \/ a = 0 /\ b <> 0 \/ a <> 0 /\ b = 0 \/ a <> 0 /\ b <> 0)%R as [H3 | [H3 | [H3 | H3]]] by lra.
  - exists 0, 0. lra.
  - exists z1, z2. lra.
  - exists 0, 0. lra.
  - assert (a + b = 0 \/ a + b <> 0)%R as [H4 | H4] by lra.
    -- exists (-z3), z4. replace (-z3) with (-1 * z3) by lia. rewrite mult_IZR. lra.
    -- exists (z1 * z4 - z2 * z3), (z2 * z4).  rewrite minus_IZR. repeat rewrite mult_IZR. pose proof H1 as H1'. rewrite H2 in H1.
       apply Rminus_eq_compat_r with (r := (IZR z3 / IZR z4)%R) in H1. replace ((IZR z3 / IZR z4 + b - IZR z3 / IZR z4)%R) with b in H1 by lra.
       rewrite H1.  destruct H3 as [H3 H3']. 
       field; split; apply not_0_IZR; try apply x_neq_0_IZR_den_neq_0 with (x := (a + b)%R) (y := z1) (z := z2); try apply x_neq_0_IZR_den_neq_0 with (x := a) (y := z3) (z := z4); auto.
Qed.

Lemma rational_mult_rev : forall a b,
  (a <> 0)%R -> rational (a * b) -> rational a -> rational b.
Proof.
  intros a b H1 H2 H3. unfold rational in *. destruct H2 as [z1 [z2 H2]]. destruct H3 as [z3 [z4 H3]].
  assert (a = 0 /\ b = 0 \/ a = 0 /\ b <> 0 \/ a <> 0 /\ b = 0 \/ a <> 0 /\ b <> 0)%R as [H4 | [H4 | [H4 | H4]]] by lra.
  - lra.
  - lra.
  - exists 0, 0. lra.
  - assert (a * b = 0 \/ a * b <> 0)%R as [H5 | H5] by lra.
    -- nra.
    -- exists (z1 * z4), (z2 * z3). repeat rewrite mult_IZR. pose proof H2 as H2'. rewrite H3 in H2.
       assert (H6 : IZR z1 <> 0%R). { apply not_0_IZR. apply x_neq_0_IZR_num_neq_0 with (x := (a * b)%R) (y := z1) (z := z2); split; auto. }
       assert (H7 : IZR z3 <> 0%R). { apply not_0_IZR. apply x_neq_0_IZR_num_neq_0 with (x := a) (y := z3) (z := z4); split; auto. }
       assert (H8 : IZR z2 <> 0%R). { apply not_0_IZR. apply x_neq_0_IZR_den_neq_0 with (x := (a * b)%R) (y := z1) (z := z2); split; auto. }
       assert (H9 : IZR z4 <> 0%R). { apply not_0_IZR. apply x_neq_0_IZR_den_neq_0 with (x := a) (y := z3) (z := z4); split; auto. }
       apply Rmult_eq_compat_r with (r := (IZR z4 / IZR z3)%R) in H2. replace ((IZR z3 / IZR z4 * b * (IZR z4 / IZR z3))%R) with b in H2 by (field; lra).
       rewrite H2. field; auto.
Qed.

Lemma lemma_2_14_a : irrational (sqrt 2 + sqrt 6).
Proof.
  assert (irrational (sqrt 2 + sqrt 6) \/ rational (sqrt 2 + sqrt 6)) as [H1 | H1].
  { unfold irrational. tauto. }
  - auto.
  - assert (sqrt 2 + sqrt 6 <> 0)%R as H2.
    { pose proof sqrt_lt_R0 2 as H2. pose proof sqrt_lt_R0 6 as H3. nra. }
    assert (rational ((sqrt 2 + sqrt 6)^2)) as H3.
    { simpl. rewrite Rmult_1_r. apply mult_rational; auto. }
    replace ((sqrt 2 + sqrt 6)^2)%R with (8 + 4 * sqrt 3)%R in H3.
    2 : 
    { 
      simpl. repeat rewrite Rmult_plus_distr_r. repeat rewrite Rmult_1_r. repeat rewrite Rmult_plus_distr_l.
      repeat rewrite sqrt_sqrt; try lra. repeat rewrite <- sqrt_mult_alt; try lra. rewrite Rmult_comm with (r1 := 2%R).
      replace (sqrt (6 * 2)) with (2 * sqrt 3)%R. 2 : { replace (6 * 2)%R with ((2 * 2) * 3)%R by lra. 
      rewrite sqrt_mult_alt; try lra. rewrite sqrt_square; lra. } lra.
    }
    apply rational_plus_rev with (a := 8%R) (b := (4 * sqrt 3)%R) in H3 as H4.
    2 : { exists 8, 1. lra. }
    apply rational_mult_rev with (a := 4%R) (b := sqrt 3) in H4 as H5.
    2 : { lra. }
    2 : { exists 4, 1. lra. }
    pose proof lemma_2_13_a as H6. unfold irrational in H6. tauto.
Qed.

Lemma lemma_2_14_b : irrational (sqrt 2 + sqrt 3).
Proof.
  assert (irrational (sqrt 2 + sqrt 3) \/ rational (sqrt 2 + sqrt 3)) as [H1 | H1].
  { unfold irrational. tauto. }
  - auto.
  - assert (sqrt 2 + sqrt 3 <> 0)%R as H2.
    { pose proof sqrt_lt_R0 2 as H2. pose proof sqrt_lt_R0 3 as H3. nra. }
    assert (rational ((sqrt 2 + sqrt 3)^2)) as H3.
    { simpl. rewrite Rmult_1_r. apply mult_rational; auto. }
    replace ((sqrt 2 + sqrt 3)^2)%R with (5 + 2 * sqrt 6)%R in H3.
    2 : 
    { 
      simpl. repeat rewrite Rmult_plus_distr_r. repeat rewrite Rmult_1_r. repeat rewrite Rmult_plus_distr_l.
      repeat rewrite sqrt_sqrt; try lra. repeat rewrite <- sqrt_mult_alt; try lra. rewrite Rmult_comm with (r1 := 2%R).
      replace (2 * 3)%R with 6%R by lra. replace (3 * 2)%R with 6%R by lra. nra.
    }
    apply rational_plus_rev with (a := 5%R) (b := (2 * sqrt 6)%R) in H3 as H4.
    2 : { exists 5, 1. lra. }
    apply rational_mult_rev with (a := 2%R) (b := sqrt 6) in H4 as H5.
    2 : { lra. }
    2 : { exists 2, 1. lra. }
    pose proof lemma_2_13_a'' as H6. unfold irrational in H6. tauto.
Qed.

Close Scope Z_scope.

Open Scope R_scope.

Lemma lemma_2_15_a : forall x p q m,
  rational p -> rational q -> x = p + sqrt q -> q >= 0 ->
    exists a b, rational a /\ rational b /\ x^m = a + b * sqrt q.
Proof.
  intros x p q m H1 H2 H3 H4. induction m as [| m' IH].
  - exists 1, 0. repeat split.
    -- exists 1%Z, 1%Z. lra.
    -- exists 0%Z, 1%Z. lra.
    -- lra.
  - destruct IH as [a [b [H5 [H6 H7]]]]. exists (p * a + q * b), (p * b + a); repeat split.
    -- apply lemma_2_12_a; apply mult_rational; auto.
    -- apply lemma_2_12_a; try apply mult_rational; auto.
    -- simpl. rewrite H7. rewrite H3. replace ((p + sqrt q) * (a + b * sqrt q)) with (p * a + p * b * sqrt q + sqrt q * a + b * (sqrt q * sqrt q)) by nra.
       rewrite sqrt_sqrt; lra. 
Qed.

Lemma lemma_2_15_b : forall p q m,
  rational p -> rational q -> q >= 0 ->
    exists a b, rational a /\ rational b /\ (p - sqrt q)^m = a - b * sqrt q.
Proof.
  intros p q m H1 H2 H3. induction m as [| m' IH].
  - exists 1, 0. repeat split.
    -- exists 1%Z, 1%Z. lra.
    -- exists 0%Z, 1%Z. lra.
    -- lra.
  - destruct IH as [a [b [H4 [H5 H6]]]]. exists (p * a + q * b), (p * b + a); repeat split.
    -- apply lemma_2_12_a; apply mult_rational; auto.
    -- apply lemma_2_12_a; try apply mult_rational; auto.
    --  simpl. rewrite H6. replace ((p - sqrt q) * (a - b * sqrt q)) with (p * a - p * b * sqrt q - sqrt q * a + b * (sqrt q * sqrt q)) by nra.
       rewrite sqrt_sqrt; lra.
Qed.

Lemma  lemma_2_16_a : forall m n : nat,
  (n > 0)%nat -> (m > 0)%nat -> ((INR m)^2 / (INR n)^2 < 2 -> INR (m + 2 * n)^2 / (INR (m + n)^2) > 2 /\
                                (INR (m + 2 * n)^2) / (INR (m + n)^2) - 2 < 2 - (INR m)^2 / (INR n)^2).
Proof.
  intros m n H1 H2 H3. split.
  - assert (H4 : INR n > 0). { apply lt_0_INR; auto. } assert (H5 : INR m > 0). { apply lt_0_INR; auto. }
    apply Rmult_lt_compat_r with (r := (INR n)^2) in H3. 2 : { nra. } field_simplify in H3. 2 : { nra. }
    apply Rmult_gt_reg_r with (r := INR (m + n)^2). simpl. rewrite Rmult_1_r. rewrite plus_INR. nra. field_simplify. 2 : { rewrite plus_INR. nra. }
    replace (INR (m + 2 * n)^2) with ((INR m)^2 + 4 * INR m * INR n + 4 * INR n^2). 
    2 : { simpl. repeat rewrite Rmult_1_r. repeat rewrite Nat.add_0_r. repeat rewrite plus_INR. nra. }
    replace (2 * INR (m + n)^2) with (2 * INR m^2 + 4 * INR m * INR n + 2 * INR n^2). 
    2 : { simpl. repeat rewrite Rmult_1_r. repeat rewrite Nat.add_0_r. repeat rewrite plus_INR. nra. }
    nra.
  - assert (INR n > 0 /\ INR m > 0) as [H4 H5] by (split; apply lt_0_INR; auto). apply Rmult_lt_reg_r with (r := INR(m + n)^2).
    rewrite plus_INR. nra. replace ((INR (m + 2 * n) ^ 2 / INR (m + n) ^ 2 - 2) * INR (m + n) ^ 2) with (INR (m + 2 * n) ^ 2 - 2 * INR (m + n) ^ 2).
    2 : { field. rewrite plus_INR. nra. } apply Rmult_lt_reg_l with (r := INR n ^ 2). nra.
    replace (INR n ^ 2 * ((2 - INR m ^ 2 / INR n ^ 2) * INR (m + n) ^ 2)) with ((INR (m + n)^2 * (2 * INR n^2 - INR m^2))).
    2 : { field. nra. } replace ((INR (m + 2 * n) ^ 2 - 2 * INR (m + n) ^ 2)) with (2 * INR n ^ 2 - INR m ^ 2).
    2 : { simpl. repeat rewrite plus_INR. repeat rewrite INR_0. repeat rewrite Rmult_1_r. repeat rewrite Rplus_0_r. nra. }
    assert (H6 : 2 * INR n ^ 2 - INR m ^ 2 > 0). {
      apply Rmult_lt_compat_r with (r := INR n^2) in H3. 2 : { nra. } field_simplify in H3. 2 : { nra. } nra.
    }
    apply Rmult_lt_reg_r with (r := 1 / (2 * INR n^2 - INR m^2)). apply Rgt_lt. unfold Rdiv. rewrite Rmult_1_l. apply Rinv_pos; nra.
    field_simplify; try nra. simpl. repeat rewrite plus_INR. nra.
Qed.

Lemma Rmult_gt_reg_neg_r : forall r r1 r2,
  r < 0 -> r1 * r > r2 * r -> r1 < r2.
Proof.
  intros. nra.
Qed.

Lemma lemma_2_16_b : forall m n : nat,
  (n > 0)%nat -> (m > 0)%nat -> ((INR m)^2 / (INR n)^2 > 2 -> INR (m + 2 * n)^2 / (INR (m + n)^2) < 2 /\
                                (INR (m + 2 * n)^2) / (INR (m + n)^2) - 2 > 2 - (INR m)^2 / (INR n)^2).
Proof.
  intros m n H1 H2 H3. split.
  - assert (H4 : INR n > 0). { apply lt_0_INR; auto. } assert (H5 : INR m > 0). { apply lt_0_INR; auto. }
    apply Rmult_gt_compat_r with (r := (INR n)^2) in H3. 2: { nra. } field_simplify in H3. 2: { nra. }
    apply Rmult_lt_reg_r with (r := INR (m + n)^2). simpl. rewrite Rmult_1_r. rewrite plus_INR. nra. field_simplify. 2: { rewrite plus_INR. nra. }
    replace (INR (m + 2 * n)^2) with ((INR m)^2 + 4 * INR m * INR n + 4 * INR n^2).
    2 : { simpl. repeat rewrite Rmult_1_r. repeat rewrite Nat.add_0_r. repeat rewrite plus_INR. nra. }
    replace (2 * INR (m + n)^2) with (2 * INR m^2 + 4 * INR m * INR n + 2 * INR n^2).
    2 : { simpl. repeat rewrite Rmult_1_r. repeat rewrite Nat.add_0_r. repeat rewrite plus_INR. nra. }
    nra.
  - assert (INR n > 0 /\ INR m > 0) as [H4 H5] by (split; apply lt_0_INR; auto). apply Rmult_gt_reg_r with (r := INR (m+n)^2).
    rewrite plus_INR. nra. replace ((INR (m + 2 * n) ^ 2 / INR (m + n) ^ 2 - 2) * INR (m + n) ^ 2) with (INR (m + 2 * n) ^ 2 - 2 * INR (m + n) ^ 2).
    2 : { field. rewrite plus_INR. nra. } apply Rmult_gt_reg_l with (r := INR n ^ 2). nra.
    replace (INR n ^ 2 * ((2 - INR m ^ 2 / INR n ^ 2) * INR (m + n) ^ 2)) with ((INR (m + n)^2 * (2 * INR n^2 - INR m^2))).
    2 : { field. nra. } replace ((INR (m + 2 * n) ^ 2 - 2 * INR (m + n) ^ 2)) with (2 * INR n ^ 2 - INR m ^ 2).
    2 : { simpl. repeat rewrite plus_INR. repeat rewrite INR_0. repeat rewrite Rmult_1_r. repeat rewrite Rplus_0_r. nra. }
    assert (H6 : 2 * INR n ^ 2 - INR m ^ 2 < 0). {
      apply Rmult_gt_compat_r with (r := INR n^2) in H3. 2 : { nra. } field_simplify in H3. 2 : { nra. } nra.
    }
    apply Rmult_gt_reg_neg_r with (r := 1 / (2 * INR n^2 - INR m^2)). apply Rlt_gt. unfold Rdiv. rewrite Rmult_1_l. apply Rinv_neg; nra.
    field_simplify; try nra. simpl. repeat rewrite plus_INR. nra.
Qed.

Lemma cross_multiply_lt : forall r1 r2 r3 r4,
  r1 > 0 -> r2 > 0 -> r3 > 0 -> r4 > 0 ->
  r1 * r4 < r2 * r3 -> r1 / r2 < r3 / r4.
Proof.
  intros r1 r2 r3 r4 H1 H2 H3 H4 H5. apply Rmult_lt_reg_r with (r := r2); 
  apply Rmult_lt_reg_r with (r := r4); field_simplify; nra.
Qed.

Lemma gte_1_INR : forall n,
  (n > 0)%nat -> INR n >= 1.
Proof.
  intros n H1. assert ((n = 1 \/ n > 1)%nat) as [H2 | H2]. { lia. }
  - rewrite H2. simpl. lra.
  - apply Rgt_ge. apply lt_1_INR. lia.
Qed.

Lemma lemma_2_16_c : forall m n : nat,
  (n > 0)%nat -> (m > 0)%nat -> INR m / INR n < sqrt 2 ->
    exists m' n', INR m / INR n < INR m' / INR n' < sqrt 2.
Proof.
  intros m n H1 H2 H3. assert (INR n >= 1 /\ INR m >= 1) as [H4 H5] by (split; apply gte_1_INR; auto).
  set (m1 := (m + 2 * n)%nat). set (n1 := (m + n)%nat).
  assert (INR m1 >= 1 /\ INR n1 >= 1) as [H6 H7]. { split. unfold m1. apply gte_1_INR. lia. unfold n1. apply gte_1_INR. lia. }
  assert ((m1 >= 1 /\ n1 >= 1)%nat) as [H8 H9] by (split; lia).
  assert (H10: (INR m^2 / INR n^2) < 2). { apply Rsqr_incrst_1 in H3. 2 : { apply Rlt_le. apply Rdiv_pos_pos; nra. } 2 : { apply sqrt_pos. }
  unfold Rsqr in H3. field_simplify in H3. 2 : { nra. } replace (sqrt 2 ^2) with 2 in H3. 2 : { simpl. rewrite Rmult_1_r. rewrite sqrt_sqrt; nra. } nra. }
  pose proof lemma_2_16_a m n H1 H2 H10 as [H11 H12]. pose proof H11 as H13. replace ((m + 2 * n)%nat) with (m1) in H13; auto. replace ((m + n)%nat) with (n1) in H13; auto.
  pose proof lemma_2_16_b m1 n1 H9 H8 H13 as [H14 H15]. 
  exists ((m1 + 2 * n1)%nat), ((m1 + n1)%nat). split.
  2 : { apply sqrt_lt_1 in H14; try nra. 2 : { apply Rlt_le. apply Rdiv_pos_pos. simpl. rewrite Nat.add_0_r. rewrite Rmult_1_r. repeat rewrite plus_INR. nra.
  simpl. rewrite Rmult_1_r. rewrite plus_INR. nra. } replace ((INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2)) with ((INR (m1 + 2 * n1) / INR (m1 + n1))^2) in H14.
  2 : { field. rewrite plus_INR. nra. } rewrite sqrt_pow2 in H14. nra. apply Rlt_le. apply Rdiv_pos_pos. simpl. rewrite Nat.add_0_r. repeat rewrite plus_INR. nra.
  repeat rewrite plus_INR. nra. }
  assert (H16 : 0 <= INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2 < 2).
  { split; auto; apply Rlt_le. apply Rdiv_pos_pos. rewrite plus_INR. rewrite mult_INR. simpl. nra. rewrite plus_INR. nra. }
  assert (H17 : INR (m1 + 2 * n1) / INR (m1 + n1) < sqrt 2). 
  { pose proof sqrt_lt_1_alt (INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2) 2 H16 as H17. rewrite sqrt_div in H17.
    - rewrite sqrt_pow2 in H17. rewrite sqrt_pow2 in H17. auto. rewrite plus_INR. nra. rewrite plus_INR. rewrite mult_INR. simpl. nra.
    - rewrite plus_INR. rewrite mult_INR. simpl. nra.
    - rewrite plus_INR. nra. }
  assert (H18 : 2 - INR (m + 2 * n) ^ 2 / INR (m + n) ^ 2 > INR m ^ 2 / INR n ^ 2 - 2) by nra.
  assert (H19 : INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2 - 2 > INR m ^ 2 / INR n ^ 2 - 2).
  { replace (INR m1 ^2) with (INR (m + 2 * n)^2) in H15. 2 : { unfold m1. auto. } 
    replace (INR n1^2) with (INR (m + n)^2) in H15. 2 : { unfold n1. auto. } nra. }
  assert (H20 : 2 - INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2 < 2 - INR m ^ 2 / INR n ^ 2) by nra.
  assert (H21 : INR m ^ 2 / INR n ^ 2 < INR (m1 + 2 * n1) ^ 2 / INR (m1 + n1) ^ 2) by nra.
  apply sqrt_lt_1 in H21; try nra. 2 : { apply Rlt_le. apply Rdiv_pos_pos; nra. }
  rewrite sqrt_div in H21; try nra. rewrite sqrt_div in H21; try nra. 2 : { rewrite plus_INR. nra. }
  rewrite sqrt_pow2 in H21; try nra. rewrite sqrt_pow2 in H21; try nra. rewrite sqrt_pow2 in H21.
  2 : { rewrite plus_INR. rewrite mult_INR. simpl. nra. } rewrite sqrt_pow2 in H21.
  2 : { rewrite plus_INR. nra. } nra.
Qed.

Open Scope Z_scope.  

Fixpoint max_list_Z (l : list Z) : Z :=
  match (l) with
  | [] => 0
  | x :: xs => Z.max x (max_list_Z xs)
  end.

Lemma in_list_le_max : forall l x,
  In x l -> x <= (max_list_Z l)%Z.
Proof.
  intros l x H. induction l as [| h t IH].
  - inversion H.
  - destruct H as [H | H].
    -- rewrite H. simpl. apply Z.le_max_l.
    -- apply IH in H. simpl. lia.
Qed.

Definition prime_list (l : list Z) : Prop := Forall Znt.prime' l.

Lemma prime_list_fold_right_pos : forall l,
  prime_list l -> fold_right Z.mul 1 l >= 0.
Proof.
  intros l H1. induction l as [| h t IH].
  - simpl. lia.
  - simpl. apply Forall_cons_iff in H1 as [H1 H2]. apply IH in H2. assert (h >= 2) as H3.
    { rewrite Znt.prime_alt in H1. apply Znt.prime_ge_2 in H1. lia. }
    lia.
Qed.

Lemma in_prime_list : forall l x,
  prime_list l -> In x l -> Znt.prime' x.
Proof.
  intros l x H1 H2. unfold prime_list in H1. rewrite Forall_forall in H1. apply H1. auto.
Qed.

Definition first_n_primes (l : list Z) : Prop :=
  NoDup l /\ prime_list l /\
    (forall x, (Znt.prime' x /\ x <= (max_list_Z l)%Z) -> In x l).

Lemma div_trans : forall a b c,
  (a | b) -> (b | c) -> (a | c).
Proof.
  intros a b c [k1 H1] [k2 H2]. unfold Z.divide. exists (k1 * k2). lia.
Qed.

Lemma prime_divides : forall z,
  z > 1 -> (exists p, Znt.prime' p /\ (p | z)).
Proof.
  intros z. assert (z <= 1 \/ z > 1) as [H1 | H1] by lia.
  - lia.
  - apply strong_induction_Z with (n := z). 2 : { lia. }
    intros n IH H2. assert (n = 2 \/ n > 2) as [H3 | H3] by lia.
    + exists 2. split.
      * rewrite Znt.prime_alt. apply Znt.prime_2.
      * exists (1). lia.
    + destruct (Znt.prime_dec n) as [H4 | H4].
      * exists n. split.
        -- rewrite Znt.prime_alt. auto.
        -- exists (1). lia.
      * rewrite <- Znt.prime_alt in H4. unfold Znt.prime' in H4. apply not_and_or in H4. destruct H4 as [H4 | H4].
        -- lia.
        -- apply not_all_ex_not in H4. destruct H4 as [p H4]. apply imply_to_and in H4. destruct H4 as [H4 H5].
           assert (p <= n) as H6 by lia. assert (p > 1) as H7 by lia. apply NNPP in H5. assert (0 <= p < n) as H9 by lia.
           specialize (IH p H9 H7). destruct IH as [p' IH]. exists p'. split.
            ++ apply IH.
            ++ apply div_trans with (b := p); (try apply IH; try apply H5).
Qed.

Lemma prime_divides_2 : forall z,
  (z < -1 \/ z > 1) -> (exists p, Znt.prime' p /\ (p | z)).
Proof.
  intros z [H1 | H2]. 
  - pose proof prime_divides (-z) as H3. assert (-z > 1) as H4 by lia. apply H3 in H4. destruct H4 as [p [H4 [r H5]]]. exists p. split; auto. exists (-r). lia.
  - apply prime_divides in H2. auto.
Qed.

Lemma prime_no_div : forall p z,
  Znt.prime' p -> (p | z) -> ~(p | z + 1).
Proof.
  intros p z H1 H2 H3. destruct H2 as [r H2]. destruct H3 as [s H3].
  assert (p | 1) as H4 by (exists (s - r); lia). assert (p >= 2) as H5.
  { rewrite Znt.prime_alt in H1. apply Znt.prime_ge_2 in H1. lia. }
  assert (p = 1) as H6. { destruct H4 as [t H4]. assert (t > 0) by lia. nia. }
  lia.
Qed.

Lemma fold_right_mul_distributive : forall (k : Z) (l : list Z),
  fold_right Z.mul k l = k * fold_right Z.mul 1 l.
Proof.
  intros k l. induction l as [| h l' IH].
  - simpl. lia.
  - simpl. rewrite IH. lia.
Qed.

Lemma fold_right_factor_divides : forall (k : Z) (l : list Z),
  (In k l) -> (k | fold_right Z.mul 1 l).
Proof.
  intros k l H. induction l as [| h l' IH].
  - inversion H.
  - simpl. destruct H as [H | H].
    -- rewrite H. apply Z.divide_factor_l.
    -- apply IH in H. destruct H as [r H]. exists (r * h). lia.
Qed.

Lemma prime_list_product_gt_1 : forall l,
  prime_list l -> fold_right Z.mul 1 l >= 1.
Proof.
  intros l H1. induction l as [| h t IH].
  - simpl. lia.
  - simpl. unfold prime_list in *. apply Forall_cons_iff in H1 as [H1 H2]. apply IH in H2.
    assert (h >= 2) as H3. { rewrite Znt.prime_alt in H1. apply Znt.prime_ge_2 in H1. lia. }
    lia.
Qed.

Lemma lemma_2_17_a : forall z : Z,
  z > 1 -> exists l : list Z,
    prime_list l /\ z = fold_right Z.mul 1 l.
Proof.
  intros z. assert (z <= 1 \/ z > 1) as [H1 | H1] by lia.
  - lia.
  - apply strong_induction_Z with (n := z). 2 : { lia. }
    intros n IH H2. assert (n = 2 \/ n > 2) as [H3 | H3] by lia.
    + exists [2]. split.
      * constructor. rewrite Znt.prime_alt. apply Znt.prime_2. constructor.
      * simpl. lia.
    + destruct (Znt.prime_dec n) as [H4 | H4].
      * exists [n]. split.
        -- constructor. rewrite Znt.prime_alt. auto. constructor.
        -- simpl. lia.
      * rewrite <- Znt.prime_alt in H4. unfold Znt.prime' in H4. apply not_and_or in H4. destruct H4 as [H4 | H4].
        -- lia.
        -- apply not_all_ex_not in H4. destruct H4 as [p H4]. apply imply_to_and in H4. destruct H4 as [H4 H5].
           apply NNPP in H5. destruct H5 as [k H5]. assert (p > 1 /\ 0 <= p < n) as [H7 H8] by lia.
           assert (k > 1 /\ 0 <= k < n) as [H9 H10] by nia.
           assert (exists l1 : list Z, prime_list l1 /\ p = fold_right Z.mul 1 l1) as [l1 H11] by (apply IH; lia).
           assert (exists l2 : list Z, prime_list l2 /\ k = fold_right Z.mul 1 l2) as [l2 H12] by (apply IH; lia).
           exists (l1 ++ l2). split.
           ++ apply Forall_app. split.
              ** apply H11.
              ** apply H12.
           ++ destruct H11 as [H11 H11']. destruct H12 as [H12 H12']. rewrite fold_right_app. rewrite <- H12'.
              rewrite fold_right_mul_distributive. rewrite <- H11'. lia.
Qed.

Lemma prime_list_product_exists_pos : forall z,
  z > 1 -> exists l : list Z,
    prime_list l /\ z = fold_right Z.mul 1 l.
Proof.
  intros z H1. pose proof (lemma_2_17_a z) as H2. apply H2 in H1. destruct H1 as [l [H1 H3]]; exists l; split; auto; try lia.
Qed.

Lemma prime_list_product_exists_neg : forall z,
  z < -1 -> exists l : list Z,
    prime_list l /\ z = -fold_right Z.mul 1 l.
Proof.
  intros z H1. pose proof (lemma_2_17_a (-z)) as H2. assert (-z > 1) as H3 by lia.
  apply H2 in H3. destruct H3 as [l [H3 H4]]; exists l; split; auto; try lia.
Qed.

Lemma prime_list_cons : forall l p,
  prime_list (p :: l) -> prime_list l /\ Znt.prime' p.
Proof.
  intros l p H1. split.
  - apply Forall_inv_tail in H1. apply H1.
  - apply Forall_inv in H1. apply H1.
Qed.

Lemma prime_list_cons_iff : forall l p,
  prime_list (p :: l) <-> prime_list l /\ Znt.prime' p.
Proof.
  intros l p. split.
  - apply prime_list_cons.
  - intros [H1 H2]. apply Forall_cons; auto.
Qed.

Lemma prime_list_app : forall l1 l2,
  prime_list (l1 ++ l2) <-> prime_list l1 /\ prime_list l2.
Proof.
  intros l1 l2. split.
  - intros H1. unfold prime_list in H1. rewrite Forall_app in H1. tauto.
  - intros [H1 H2]. unfold prime_list. rewrite Forall_app. tauto.
Qed.

Lemma in_div_fold_right : forall l z,
  In z l -> (z | fold_right Z.mul 1 l).
Proof.
  intros l z H. induction l as [| h t IH].
  - inversion H.
  - simpl. destruct H as [H | H].
    -- rewrite H. apply Z.divide_factor_l.
    -- apply IH in H. destruct H as [r H]. exists (r * h). lia.
Qed.

Lemma divide_factor_l : forall a b c,
  (b | c) -> (a * b | a * c).
Proof.
  intros a b c [k H]. exists k. lia.
Qed.

Lemma count_mul_div_fold_right : forall l z,
  In z l -> (z ^ (Z.of_nat (count_occ Z.eq_dec l z)) | fold_right Z.mul 1 l).
Proof.
  intros l z H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct H1 as [H1 | H1].
    -- rewrite H1. destruct (Z.eq_dec z z) as [H2 | H2]; try contradiction. clear H2.
       assert (In z t \/ ~ In z t) as [H2 | H2] by apply classic.
       + replace (Z.of_nat (S (count_occ Z.eq_dec t z))) with (Z.succ (Z.of_nat (count_occ Z.eq_dec t z))) by lia.
         rewrite Z.pow_succ_r. 2 : { lia. } apply divide_factor_l. apply IH; auto.
       + apply (count_occ_not_In Z.eq_dec) in H2. rewrite H2. simpl. exists (fold_right Z.mul 1 t). lia. 
    -- pose proof (Z.eq_dec h z) as [H2 | H2].
       + rewrite H2. destruct (Z.eq_dec z z) as [H3 | H3]; try contradiction. clear H3.
         replace (Z.of_nat (S (count_occ Z.eq_dec t z))) with (Z.succ (Z.of_nat (count_occ Z.eq_dec t z))) by lia.
         rewrite Z.pow_succ_r. 2 : { lia. } apply divide_factor_l. apply IH; auto.
       + destruct (Z.eq_dec h z) as [H3 | H3]; try contradiction. apply IH in H1. destruct H1 as [r H1]. exists (r * h). lia.
Qed.

Lemma p_div_fold_right_In : forall l p,
  prime_list l -> Znt.prime' p -> (p | fold_right Z.mul 1 l) -> In p l.
Proof.
  intros l p H1 H2 H3. induction l as [| h t IH].
  - simpl in H3. rewrite Znt.prime_alt in H2. apply Znt.prime_ge_2 in H2. destruct H3 as [r1 H3]. assert (r1 = 1) as H4 by lia. lia.
  - simpl in H3. apply prime_list_cons in H1 as [H1 H1']. destruct (Z.eq_dec h p) as [H6 | H6].
    + rewrite H6. left. reflexivity.
    + right. apply IH. rewrite Znt.prime_alt in H2. auto. apply Znt.prime_mult in H3. 2 : { rewrite Znt.prime_alt in H2. auto. }
      assert (H7 : ~(p | h)). { intros H7. apply Znt.prime_div_prime in H7; try lia; rewrite Znt.prime_alt in H1', H2; auto. }
      tauto.
Qed.

Lemma p_notin_ndiv_fold_right : forall l p,
  prime_list l -> Znt.prime' p -> ~In p l -> ~(p | fold_right Z.mul 1 l).
Proof.
  intros l p H1 H2 H3 H4. apply p_div_fold_right_In in H4; auto.
Qed.

Lemma div_a_mul_p_pow : forall a b c d,
  (c > 0)%nat -> a = b * d^(Z.of_nat c) -> (d | a).
Proof.
  intros a b c p H1 H2. destruct c; try lia. rewrite Nat2Z.inj_succ in H2. rewrite Z.pow_succ_r in H2; try lia.
  exists (b * p ^ Z.of_nat c). lia.
Qed.

Lemma div_mul_factor : forall a b c d,
  b <> 0 -> a * b = c * d -> (b | d) -> a = c * (d / b).
Proof.
  intros a b c d H1 H2 [k H3]. rewrite H3. rewrite Z.div_mul; auto. rewrite H3 in H2. apply Z.mul_cancel_l with (p := b); auto. lia.
Qed.

Lemma z_pow_zero : forall a : Z,
  a <> 0 -> 0^a = 0.
Proof.
  intros a H1. assert (a < 0 \/ a = 0 \/ a = 1 \/ a > 1) as [H2 | [H2 | [H2 | H2]]] by lia.
  - rewrite Z.pow_neg_r; lia.
  - rewrite H2. lia.
  - rewrite H2. lia.
  - replace a with (Z.succ (a - 1)) by lia. rewrite Z.pow_succ_r; lia.
Qed.

Lemma fold_right_div_pow_eq_remove_fold_right : forall l z,
  z <> 0 ->
  fold_right Z.mul 1 l / (z ^ (Z.of_nat (count_occ Z.eq_dec l z))) = fold_right Z.mul 1 (remove Z.eq_dec z l).
Proof.
  intros l z H1. induction l as [| h t IH].
  - simpl. apply Z.div_1_r.
  - assert (In z (h :: t) \/ ~ In z (h :: t)) as [H2 | H2] by apply classic.
    -- simpl. destruct (Z.eq_dec h z) as [H3 | H3].
       + rewrite H3. destruct (Z.eq_dec z z) as [H4 | H4]; try contradiction. clear H4.
         assert (In z t \/ ~ In z t) as [H4 | H4] by apply classic.
         * rewrite <- IH. rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r. 2 : { lia. } pose proof (count_mul_div_fold_right t z H4) as [r H5].
           rewrite H5. rewrite Z.div_mul. 2 : { apply (count_occ_In Z.eq_dec) in H4. apply Z.pow_nonzero. lia. lia. } rewrite Z.mul_comm. rewrite <- Z.mul_assoc.
              replace (z^Z.of_nat (count_occ Z.eq_dec t z) * z) with (z * z^Z.of_nat (count_occ Z.eq_dec t z)) by lia. rewrite Z.div_mul; try lia.
              assert (H6 : z ^ Z.of_nat (count_occ Z.eq_dec t z) <> 0). { apply Z.pow_nonzero; lia. } lia.
         * replace (count_occ Z.eq_dec t z) with (0%nat). 2 : { apply (count_occ_not_In Z.eq_dec) in H4. lia. }
           replace (remove Z.eq_dec z t) with t. 2 : { apply (notin_remove Z.eq_dec) in H4. auto. } rewrite Z.mul_comm. replace (Z.of_nat 1) with 1 by lia.
           rewrite Z.pow_1_r. rewrite Z.div_mul; try lia.
       + destruct (Z.eq_dec z h) as [H4 | H4]; try lia. clear H4. simpl. rewrite <- IH. destruct H2 as [H2 | H2]; try contradiction. pose proof (count_mul_div_fold_right t z H2) as [r H4].
         rewrite H4. rewrite Z.div_mul. 2 : { apply (count_occ_In Z.eq_dec) in H2. apply Z.pow_nonzero. lia. lia. } rewrite Z.mul_comm. rewrite <- Z.mul_assoc.
         replace (z^Z.of_nat (count_occ Z.eq_dec t z) * h) with (h * z^Z.of_nat (count_occ Z.eq_dec t z)) by lia. rewrite Z.mul_assoc. rewrite Z.div_mul; try lia.
         apply (count_occ_In Z.eq_dec) in H2. apply Z.pow_nonzero; lia.
    -- replace (remove Z.eq_dec z (h :: t)) with (h :: t). 2 : { apply (notin_remove Z.eq_dec) in H2. auto. } 
       replace (count_occ Z.eq_dec (h :: t) z) with (0%nat). 2 : { apply (count_occ_not_In Z.eq_dec) in H2. lia. } simpl. rewrite Z.div_1_r. lia.
Qed.

Lemma p_ndiv_fold_right : forall l p,
  prime_list l -> In p l -> ~(p | (fold_right Z.mul 1 l / p ^ (Z.of_nat (count_occ Z.eq_dec l p)))).
Proof.
  intros l p H1 H2. rewrite fold_right_div_pow_eq_remove_fold_right. 
  2 : { apply in_prime_list in H2; auto. rewrite Znt.prime_alt in H2. apply Znt.prime_ge_2 in H2. lia. }
  intros H3. assert (~In p (remove Z.eq_dec p l)) as H4. { intros H4. apply (in_remove Z.eq_dec) in H4. lia. }
  apply H4. apply p_div_fold_right_In; auto. 2 : { apply in_prime_list in H2; auto. } unfold prime_list in *.
  rewrite Forall_forall in *. intros x H5. apply H1. apply in_remove in H5. tauto.
Qed.

Lemma z_pow_div_z_div : forall a b c,
  c >= 1 -> (a^c | b) -> (a | b).
Proof.
  intros a b c H1 [k H2]. exists (k * a^(Z.pred c)). rewrite H2.
  - assert (c = 1 \/ c > 1) as [H3 | H3] by lia.
    + rewrite H3. simpl. lia.
    + assert (H4 : exists d, c = Z.succ d) by (exists (Z.pred c); lia). destruct H4 as [d H4]. rewrite H4. rewrite Z.pow_succ_r. 2 : { lia. }
      replace (Z.pred (Z.succ d)) with d by lia. lia.
Qed.

Lemma z_mul_div : forall a b c,
  c <> 0 ->
  (c | b) -> a * (b / c) = (a * b) / c.
Proof.
  intros a b c H1 [r1 H2]. rewrite H2. rewrite Z.div_mul; auto. 
  rewrite Z.mul_assoc. rewrite Z.div_mul; auto.
Qed.

Lemma z_pow_mult : forall a b c,
  a >= 0 -> b >= 0 -> c >= 0 -> a^(b) * a^(c) = a^(b + c).
Proof.
  intros a b c H1 H2 H3. rewrite Z.pow_add_r; lia.
Qed.

Lemma prime_factorization_unique : forall l1 l2 z p,
  prime_list l1 -> prime_list l2 -> z = fold_right Z.mul 1 l1 -> z = fold_right Z.mul 1 l2 -> 
  count_occ Z.eq_dec l1 p = count_occ Z.eq_dec l2 p.
Proof.
  intros l1 l2 z p H1 H2 H3 H4.
  pose proof (lt_eq_lt_dec (count_occ Z.eq_dec l1 p) (count_occ Z.eq_dec l2 p)) as [[H5 | H5] | H5].
  2 : { auto. }
  - assert (H6 : In p l2). { apply (count_occ_In Z.eq_dec); lia. } pose proof (count_mul_div_fold_right l2 p H6) as H7.
    rewrite <- H4 in H7. assert (count_occ Z.eq_dec l1 p = 0 \/ count_occ Z.eq_dec l1 p > 0)%nat as [H8 | H8] by lia.
    -- assert (H9 : ~In p l1). { intros H9. apply (count_occ_not_In Z.eq_dec) in H9. lia. lia. } 
       assert (H10 : ~(p | fold_right Z.mul 1 l1)). { apply p_notin_ndiv_fold_right; auto. apply in_prime_list in H6; auto. }
       rewrite <- H3 in H10. assert (H11 : (p | z)). { apply z_pow_div_z_div with (c := Z.of_nat (count_occ Z.eq_dec l2 p)); auto; lia. } tauto.
    -- assert (H9 : In p l1). { apply (count_occ_In Z.eq_dec); lia. } pose proof (count_mul_div_fold_right l1 p H9) as H10.
       rewrite <- H3 in H10. assert (H11 : (p | z / p ^ (Z.of_nat (count_occ Z.eq_dec l1 p)))).
       { destruct H7 as [r1 H7]. destruct H10 as [r2 H10]. exists (r1 * p ^ Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p - 1)). rewrite H10. rewrite Z.div_mul. 
         2 : { apply Z.pow_nonzero. apply in_prime_list in H6; auto. apply Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia. lia. }
         rewrite <- Z.mul_assoc. rewrite Z.mul_comm with (m := p). rewrite <- Z.pow_succ_r; try lia.
         replace (Z.succ (Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p - 1))) with (Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p)) by lia.
         rewrite Nat2Z.inj_sub; try lia. rewrite Z.pow_sub_r; try lia. 2 : { apply in_prime_list in H6; auto. apply Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia. }
         assert (H12 : (p ^ Z.of_nat (count_occ Z.eq_dec l1 p) | p ^ Z.of_nat (count_occ Z.eq_dec l2 p))). 
         { exists (p ^ (Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p))). rewrite z_pow_mult; try lia. 
           2 : { apply in_prime_list in H6; auto. apply Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia. }
           replace (Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p) + Z.of_nat (count_occ Z.eq_dec l1 p)) with (Z.of_nat (count_occ Z.eq_dec l2 p)) by lia. lia. 
         }
         rewrite z_mul_div; auto. 2 : { apply in_prime_list in H6; auto. apply Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia. }
         rewrite <- H7. rewrite H10. rewrite Z.div_mul; auto. apply in_prime_list in H6; auto. apply Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia.
       }
       pose proof p_ndiv_fold_right l1 p H1 H9 as H12. rewrite <- H3 in H12. tauto.
  - assert (H6 : In p l1). { apply (count_occ_In Z.eq_dec); lia. } pose proof (count_mul_div_fold_right l1 p H6) as H7.
    rewrite <- H3 in H7. assert (count_occ Z.eq_dec l2 p = 0 \/ count_occ Z.eq_dec l2 p > 0)%nat as [H8 | H8] by lia.
    -- assert (H9 : ~In p l2). { intros H9. apply (count_occ_not_In Z.eq_dec) in H9. lia. lia. } 
       assert (H10 : ~(p | fold_right Z.mul 1 l2)). { apply p_notin_ndiv_fold_right; auto. apply in_prime_list in H6; auto. }
       rewrite <- H4 in H10. assert (H11 : (p | z)). { apply z_pow_div_z_div with (c := Z.of_nat (count_occ Z.eq_dec l1 p)); auto; lia. }
       tauto.
    -- assert (H9 : In p l2). { apply (count_occ_In Z.eq_dec); lia. } pose proof (count_mul_div_fold_right l2 p H9) as H10.
       rewrite <- H4 in H10. assert (H11 : (p | z / p ^ (Z.of_nat (count_occ Z.eq_dec l2 p)))).
       { destruct H7 as [r1 H7]. destruct H10 as [r2 H10]. exists (r1 * p ^ Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p - 1)). rewrite H10. rewrite Z.div_mul.
         2 : { apply Z.pow_nonzero. apply in_prime_list in H6; auto. apply Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia. lia. }
         rewrite <- Z.mul_assoc. rewrite Z.mul_comm with (m := p). rewrite <- Z.pow_succ_r; try lia.
         replace (Z.succ (Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p - 1))) with (Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p)) by lia.
         rewrite Nat2Z.inj_sub; try lia. rewrite Z.pow_sub_r; try lia. 2 : { apply in_prime_list in H6; auto. apply Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia. }
         assert (H12 : (p ^ Z.of_nat (count_occ Z.eq_dec l2 p) | p ^ Z.of_nat (count_occ Z.eq_dec l1 p))). 
         { exists (p ^ (Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p))). rewrite z_pow_mult; try lia. 
           2 : { apply in_prime_list in H6; auto. apply Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia. }
           replace (Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p) + Z.of_nat (count_occ Z.eq_dec l2 p)) with (Z.of_nat (count_occ Z.eq_dec l1 p)) by lia. lia. 
         }
         rewrite z_mul_div; auto. 2 : { apply in_prime_list in H6; auto. apply Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia. }
         rewrite <- H7. rewrite H10. rewrite Z.div_mul; auto. apply in_prime_list in H6; auto. apply Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia.
       }
       pose proof p_ndiv_fold_right l2 p H2 H9 as H12. rewrite <- H4 in H12. tauto.
Qed.

Lemma fold_right_mult_app_Z : forall l1 l2,
  fold_right Z.mul 1 (l1 ++ l2) = fold_right Z.mul 1 l1 * fold_right Z.mul 1 l2.
Proof.
  intros l1 l2. induction l1 as [| h1 t1 IH].
  - replace (fold_right Z.mul 1 []) with 1 by reflexivity. replace ([] ++ l2) with l2 by reflexivity. lia.
  - simpl. rewrite IH. lia.
Qed.

Fixpoint repeat_app (l : list Z) (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => l ++ repeat_app l n'
  end. 

Lemma in_repeat_app : forall l n z,
  In z (repeat_app l n) -> In z l.
Proof.
  intros l n z H. induction n as [| n' IH].
  - simpl in H. contradiction.
  - simpl in H. apply in_app_or in H. destruct H as [H | H]; auto.
Qed.

Lemma count_occ_repeat_app : forall l n z,
  count_occ Z.eq_dec (repeat_app l n) z = (n * count_occ Z.eq_dec l z)%nat.
Proof.
  intros l n z. induction n as [| n' IH].
  - simpl. lia.
  - simpl. rewrite count_occ_app. rewrite IH. lia.
Qed.

Lemma count_occ_repeat_eq : forall n z,
  count_occ Z.eq_dec (repeat z n) z = n.
Proof.
  intros n z. induction n as [| n' IH].
  - simpl. lia.
  - simpl. destruct (Z.eq_dec z z) as [H1 | H1].
    + rewrite IH. lia.
    + contradiction.
Qed.

Lemma count_occ_repeat_possible_equal : forall h n z,
  count_occ Z.eq_dec (repeat h n) z = (if Z.eq_dec h z then n else 0)%nat.
Proof.
  intros h n z. induction n as [| n' IH].
  - simpl. destruct (Z.eq_dec h z); lia.
  - simpl. destruct (Z.eq_dec h z) as [H1 | H1].
    + rewrite H1 in *. lia.
    + apply IH.
Qed.

Lemma count_occ_2n_exist_app : forall l1 l2 n,
  (forall z, (count_occ Z.eq_dec l2 z = 2 * n * count_occ Z.eq_dec l1 z)%nat) ->
    exists l3, forall z, (count_occ Z.eq_dec l2 z = count_occ Z.eq_dec (l3 ++ l3) z)%nat.
Proof.
  intros l1 l2 n H1. destruct l1 as [| h t].
  - exists l2. intros z. simpl in H1. rewrite Nat.mul_0_r in H1. apply count_occ_inv_nil in H1. rewrite H1. reflexivity.
  - exists (repeat h n ++ repeat_app t n). intros z. specialize (H1 z). rewrite H1. repeat rewrite count_occ_app. 
    repeat rewrite count_occ_repeat_app. destruct (Z.eq_dec h z) as [H2 | H2].
    -- rewrite H2. repeat rewrite count_occ_repeat_eq. simpl. destruct (Z.eq_dec z z) as [H3 | H3]; try contradiction. lia.
    -- repeat rewrite count_occ_repeat_possible_equal. destruct (Z.eq_dec z h) as [H3 | H3].
       + rewrite H3. simpl. destruct (Z.eq_dec h h) as [H4 | H4]; try contradiction. lia.
       + destruct (Z.eq_dec h z) as [H4 | H4]; try contradiction. simpl. 
         destruct (Z.eq_dec h z) as [H5 | H5]; try contradiction. lia.
Qed.

Lemma repeat_app_nil : forall (l : list Z) n,
  repeat_app [] n = [].
Proof.
  intros l n. induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma z_square_even_primes : forall z,
  (z > 1)%Z -> exists l, prime_list l /\ z^2 = fold_right Z.mul 1 l /\ (forall p, Nat.Even (count_occ Z.eq_dec l p)).
Proof.
  intros z H1. pose proof (lemma_2_17_a z H1) as [l [H2 H3]].
  exists (l ++ l). repeat split.
  - apply Forall_app; split; auto.
  - rewrite fold_right_mult_app_Z. lia.
  - intros p. rewrite count_occ_app. exists (count_occ Z.eq_dec l p). lia.
Qed.

Lemma fold_right_repeat_app : forall l n,
  fold_right Z.mul 1 (repeat_app l n) = fold_right Z.mul 1 l ^ Z.of_nat n.
Proof.
  intros l n. induction n as [| n' IH].
  - simpl. lia.
  - replace (fold_right Z.mul 1 (repeat_app l (S n'))) with (fold_right Z.mul 1 (l ++ repeat_app l n')) by reflexivity.
    rewrite fold_right_mult_app_Z. rewrite IH. rewrite <- Z.pow_succ_r; lia.
Qed.

Lemma z_pow_factor_primes : forall z k,
  (z > 1)%Z -> exists l, prime_list l /\ z^Z.of_nat k = fold_right Z.mul 1 l /\ (forall p, exists q, (count_occ Z.eq_dec l p) = q * k)%nat.
Proof.
  intros z k H1. pose proof (lemma_2_17_a z H1) as [l [H2 H3]].
  exists (repeat_app l k). repeat split.
  - apply Forall_forall. intros x H4. apply in_repeat_app in H4. apply in_prime_list in H4; auto.
  - rewrite fold_right_repeat_app. rewrite H3. lia.
  - intros p. rewrite count_occ_repeat_app. exists (count_occ Z.eq_dec l p). lia.
Qed.

Fixpoint remove_one {A : Type} (eq_dec : forall (x y : A), {x = y} + {x <> y})
                        (a : A) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => if eq_dec x a then xs else x :: remove_one eq_dec a xs
  end.

Fixpoint reduce_freq_to_half {A : Type} (eq_dec : forall (x y : A), {x = y} + {x <> y})
                                      (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => 
      let freq := count_occ eq_dec l x in
      repeat x (Nat.div2 freq) ++ remove eq_dec x (reduce_freq_to_half eq_dec xs)
  end.  

Fixpoint reduce_freq_by_factor {A : Type} (eq_dec : forall (x y : A), {x = y} + {x <> y})
                                (k : nat) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs =>
      let freq := count_occ eq_dec l x in
      repeat x (freq / k) ++ remove eq_dec x (reduce_freq_by_factor eq_dec k xs)
  end.

Lemma remove_one_In : forall {A : Type} eq_dec (a : A) l,
  In a l -> count_occ eq_dec (remove_one eq_dec a l) a = pred (count_occ eq_dec l a).
Proof.
  intros A eq_dec a l H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct (eq_dec h a) as [H2 | H2].
    + simpl. reflexivity.
    + simpl. destruct H1 as [H1 | H1].
      * rewrite H1 in H2. contradiction.
      * rewrite IH; auto. destruct (eq_dec h a) as [H3 | H3]; try contradiction. reflexivity.
Qed.

Lemma remove_one_not_In : forall {A : Type} eq_dec (a : A) l,
  ~In a l -> remove_one eq_dec a l = l.
Proof.
  intros A eq_dec a l H1. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (eq_dec h a) as [H2 | H2].
    + rewrite H2 in H1. rewrite not_in_cons in H1. tauto.
    + simpl. rewrite IH; auto. rewrite not_in_cons in H1. tauto.
Qed.

Lemma count_occ_remove_one_neq : forall {A : Type} eq_dec (a b : A) l,
  a <> b -> count_occ eq_dec (remove_one eq_dec a l) b = count_occ eq_dec l b.
Proof.
  intros A eq_dec a b l H1. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (eq_dec h a) as [H2 | H2].
    + destruct (eq_dec h b) as [H3 | H3].
      * rewrite H3 in H2. rewrite H2 in H1. contradiction.
      * reflexivity.
    + destruct (eq_dec h b) as [H3 | H3].
      * rewrite H3. simpl. destruct (eq_dec b b) as [H4 | H4]; try contradiction. rewrite IH. reflexivity.
      * simpl. destruct (eq_dec h b) as [H4 | H4]; try contradiction. rewrite IH. reflexivity.
Qed.

Lemma Z_div_mult_good : forall a b, 
  (a <> 0) -> a * b / a = b.
Proof.
  intros a b H1. rewrite Z.mul_comm. rewrite Z.div_mul; auto.
Qed.

Lemma In_0_fold_right_eq_0 : forall l,
  In 0 l -> fold_right Z.mul 1 l = 0.
Proof.
  intros l H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct H1 as [H1 | H1].
    + rewrite H1. lia.
    + apply IH in H1. lia.
Qed.

Lemma contra_2 : forall P Q,
  (P -> Q) -> (~Q -> ~P).
Proof.
  tauto.
Qed.

Lemma not_in_0_fold_right_neq_0 : forall l,
  ~In 0 l -> fold_right Z.mul 1 l <> 0.
Proof.
  intros l H1. induction l as [| h t IH].
  - simpl. lia.
  - simpl. apply not_in_cons in H1 as [H1 H1']. destruct (Z.eq_dec h 0) as [H2 | H2].
    + rewrite H2. lia.
    + apply IH in H1'. lia.
Qed.

Lemma fold_right_remove_one_In : forall a l,
  ~In 0 l -> In a l -> fold_right Z.mul 1 (remove_one Z.eq_dec a l) = fold_right Z.mul 1 l / a.
Proof.
  intros a l H1 H2. induction l as [| h t IH].
  - inversion H2.
  - simpl. destruct (Z.eq_dec h a) as [H3 | H3].
    + rewrite H3. replace (a * fold_right Z.mul 1 t / a) with (fold_right Z.mul 1 t).
      2 : { rewrite <- Z.mul_comm. rewrite Z.div_mul; auto. apply not_in_cons in H1. lia. }
      lia.
    + simpl. destruct H2 as [H2 | H2]; try contradiction.
      rewrite IH; auto. 2 : { apply not_in_cons in H1. tauto. }
      apply in_div_fold_right in H2 as [r H2]. rewrite H2. rewrite Z.div_mul. 
      2 : { apply not_in_cons in H1 as [H1 H1']. apply not_in_0_fold_right_neq_0 in H1'. lia. }
      rewrite Z.mul_assoc. rewrite Z.div_mul; auto. apply not_in_cons in H1. 
      destruct H1 as [H1 H1']. apply not_in_0_fold_right_neq_0 in H1'. lia.
Qed.

Lemma fold_right_0_In : forall l,
  In 0 l -> fold_right Z.mul 1 l = 0.
Proof.
  intros l H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct H1 as [H1 | H1].
    + rewrite H1. lia.
    + apply IH in H1. lia.
Qed.

Lemma in_remove_in : forall a b l,
  In a (remove_one Z.eq_dec b l) -> In a l.
Proof.
  intros a b l H1. induction l as [| h t IH].
  - contradiction.
  - simpl in H1. destruct (Z.eq_dec h b) as [H2 | H2].
    + simpl. tauto.
    + simpl. destruct H1 as [H1 | H1].
      * left. auto.
      * tauto.
Qed.

Lemma remove_one_not_in_remove_one : forall (a b : Z) l,
  ~In a l -> ~In a (remove_one Z.eq_dec b l).
Proof.
  intros a b l H1 H2. apply H1. apply in_remove_in in H2. auto.
Qed.

Lemma count_occ_equ_fold_right : forall l1 l2,
  (forall z, (count_occ Z.eq_dec l2 z = count_occ Z.eq_dec l1 z)%nat) ->
  fold_right Z.mul 1 l1 = fold_right Z.mul 1 l2.
Proof.
  intros l1 l2 H1. assert (In 0 l2 \/ ~In 0 l2) as [H0 | H0] by apply classic.
  - specialize (H1 0). assert (In 0 l1). { apply (count_occ_In Z.eq_dec) in H0. apply (count_occ_In Z.eq_dec). lia. }
    repeat rewrite fold_right_0_In; auto.
  - assert (H0' : ~In 0 l1). { intros H2. apply H0. apply (count_occ_In Z.eq_dec) in H2. apply (count_occ_not_In Z.eq_dec) in H0. specialize (H1 0). lia. } 
    generalize dependent l2. induction l1 as [| h t IH].
    intros l2 H1. simpl in *. apply count_occ_inv_nil in H1. rewrite H1. reflexivity.
  -- intros l2 H1 H2. simpl. simpl in H0'. apply not_or_and in H0' as [H0' H0'']. specialize (IH H0'' (remove_one Z.eq_dec h l2)). rewrite IH.
    2 : { 
      intros z. assert (In z l2 \/ ~In z l2) as [H3 | H3] by apply classic.
      - assert (h = z \/ h <> z) as [H4 | H4] by apply classic.
         + rewrite H4 in *. specialize (H1 z). rewrite count_occ_cons_eq in H1; auto. rewrite remove_one_In; auto. lia.
         + specialize (H1 z). rewrite count_occ_cons_neq in H1; auto. rewrite <- H1. rewrite count_occ_remove_one_not_eq; auto.
       - assert (h = z \/ h <> z) as [H4 | H4] by apply classic.
         + rewrite H4 in *. specialize (H1 z). apply (count_occ_not_In Z.eq_dec) in H3. rewrite H3 in H1. rewrite count_occ_cons_eq in H1; auto. lia.
         + specialize (H1 z). rewrite count_occ_cons_neq in H1; auto. rewrite <- H1. rewrite count_occ_remove_one_not_eq; auto.
    }
    2 : { intros H3. apply (remove_one_not_in_remove_one 0 h l2) in H2. tauto. }
    specialize (H1 h). rewrite count_occ_cons_eq in H1; auto. assert (In h l2) as H3.
    { rewrite (count_occ_In Z.eq_dec). lia. } rewrite fold_right_remove_one_In; auto. apply in_div_fold_right in H3 as [r H3]. rewrite H3. rewrite Z.div_mul; auto; lia.
Qed.

Lemma count_occ_double_n : forall z l1 l2 n,
  count_occ Z.eq_dec l2 z = (2 * n * count_occ Z.eq_dec l1 z)%nat -> count_occ Z.eq_dec (repeat_app l1 (2 * n)%nat) z = count_occ Z.eq_dec l2 z.
Proof.
  intros z l1 l2 n H1. rewrite count_occ_repeat_app. lia. 
Qed.

Lemma count_occ_double_n_prime : forall l1 l2 n,
  (forall z, (count_occ Z.eq_dec l2 z = 2 * n * count_occ Z.eq_dec l1 z)%nat) ->
  (forall z, (count_occ Z.eq_dec (repeat_app l1 (2 * n)) z = count_occ Z.eq_dec l2 z)%nat).
Proof.
  intros l1 l2 n H1 z. specialize (H1 z). rewrite count_occ_repeat_app. lia.
Qed.

Lemma fold_right_mult_repeat_app_Z : forall l n,
  fold_right Z.mul 1 (repeat_app l n) = fold_right Z.mul 1 l ^ (Z.of_nat n).
Proof.
  intros l n. induction n as [| n' IH].
  - simpl. lia.
  - replace (fold_right Z.mul 1 (repeat_app l (S n'))) with (fold_right Z.mul 1 (l ++ repeat_app l n')) by reflexivity. rewrite fold_right_mult_app_Z. rewrite IH.
    rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r. 2 : { lia. } lia.  
Qed.

Lemma fold_right_double_n_count_square : forall l1 l2 (n : nat),
  (forall z, (count_occ Z.eq_dec l2 z = 2 * n * count_occ Z.eq_dec l1 z)%nat) ->
  (fold_right Z.mul 1 l1)^(Z.of_nat (2 * n)) = fold_right Z.mul 1 l2.
Proof.
  intros l1 l2 n H1. pose proof (count_occ_double_n_prime l1 l2 n H1) as H2. apply count_occ_equ_fold_right in H2. 
  rewrite H2. rewrite fold_right_mult_repeat_app_Z. reflexivity.
Qed.

Lemma even_count_occ_cons_eq : forall h t z,
  Nat.Even (count_occ Z.eq_dec (h :: t) z) -> z = h -> Nat.Odd (count_occ Z.eq_dec t z).
Proof.
  intros h t z H1 H2. induction t as [| h' t' IH].
  - rewrite H2 in H1. simpl in H1. destruct (Z.eq_dec h h) as [H3 | H3]; try lia. 
    assert (Nat.Odd 1) as H4. { unfold Nat.Odd. exists 0%nat. lia. } assert (~Nat.Even 1) as H5. { unfold Nat.Even. intros [k H5]. lia. }
    tauto.
  - rewrite H2. simpl. destruct (Z.eq_dec h' h) as [H3 | H3].
    + rewrite H3 in H1. rewrite H2 in H1. simpl in H1. destruct (Z.eq_dec h h) as [H4 | H4]; try lia.
      apply Nat.Even_succ. apply H1.
    + rewrite H2 in *. apply IH. simpl in *. destruct (Z.eq_dec h h) as [H4 | H4]; try lia. rewrite Nat.Even_succ. apply IH.
      destruct (Z.eq_dec h' h) as [H5 | H5]; try contradiction. apply H1.
Qed.

Lemma even_count_odd_cons_neq : forall h t z,
  Nat.Even (count_occ Z.eq_dec (h :: t) z) -> z <> h -> Nat.Even (count_occ Z.eq_dec t z).
Proof.
  intros h t z H1 H2. induction t as [| h' t' IH].
  - simpl. exists 0%nat. lia.
  - simpl in *. repeat destruct (Z.eq_dec h' h) as [H3 | H3]; repeat destruct (Z.eq_dec h' z) as [H4 | H4]; 
    repeat destruct (Z.eq_dec h z) as [H5 | H5]; try lia; auto.
Qed.

Lemma count_occ_remove_neq : forall h t z,
  h <> z -> count_occ Z.eq_dec (remove Z.eq_dec h t) z = count_occ Z.eq_dec t z. 
Proof.
  intros h t z H1. induction t as [| h' t' IH].
  - simpl. reflexivity.
  - simpl. repeat (simpl; destruct (Z.eq_dec h h') as [H2 | H2]); repeat (simpl; destruct (Z.eq_dec h' z) as [H3 | H3]); try lia.
Qed.

Lemma count_occ_0_count_occ_reduce_0 : forall l1 z,
  count_occ Z.eq_dec l1 z = 0%nat -> count_occ Z.eq_dec (reduce_freq_to_half Z.eq_dec l1) z = 0%nat.
Proof.
  intros l1 z H1. induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl in H1. destruct (Z.eq_dec h z) as [H2 | H2]; try lia. pose proof H1 as H1'. apply IH in H1. clear IH. simpl.
    destruct (Z.eq_dec h h) as [H3 | H3]; try lia. rewrite count_occ_app. simpl. rewrite count_occ_repeat_neq; auto.
    rewrite count_occ_remove_neq; auto.
Qed.

Lemma count_occ_0_count_occ_reduce_factor_0 : forall l1 z k,
  count_occ Z.eq_dec l1 z = 0%nat -> count_occ Z.eq_dec (reduce_freq_by_factor Z.eq_dec k l1) z = 0%nat.
Proof.
  intros l1 z k H1. induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl in H1. destruct (Z.eq_dec h z) as [H2 | H2]; try lia. pose proof H1 as H1'. apply IH in H1. clear IH. simpl.
    destruct (Z.eq_dec h h) as [H3 | H3]; try lia. rewrite count_occ_app. simpl. rewrite count_occ_repeat_neq; auto.
    rewrite count_occ_remove_neq; auto.
Qed.

Lemma remove_repeat : forall h n,
  remove Z.eq_dec h (repeat h n) = [].
Proof.
  intros h n. induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. destruct (Z.eq_dec h h) as [H1 | H1]; try lia. apply IH.
Qed.

Lemma count_occ_reduce_freq_not_in : forall l1 z,
  ~In z l1 -> count_occ Z.eq_dec (reduce_freq_to_half Z.eq_dec l1) z = 0%nat.
Proof.
  intros l1 z H1. induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl in H1. apply not_in_cons in H1 as [H1 H1']. simpl. destruct (Z.eq_dec h z) as [H2 | H2].
    + rewrite H2 in H1. contradiction.
    + rewrite count_occ_app. simpl. rewrite count_occ_repeat_neq; auto. rewrite count_occ_remove_neq; auto.
Qed.

Lemma count_occ_reduce_freq_factor_not_in : forall l1 z k,
  ~In z l1 -> count_occ Z.eq_dec (reduce_freq_by_factor Z.eq_dec k l1) z = 0%nat.
Proof.
  intros l1 z k H1. induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl in H1. apply not_in_cons in H1 as [H1 H1']. simpl. destruct (Z.eq_dec h z) as [H2 | H2].
    + rewrite H2 in H1. contradiction.
    + rewrite count_occ_app. simpl. rewrite count_occ_repeat_neq; auto. rewrite count_occ_remove_neq; auto.
Qed.

Lemma remove_repeat_neq : forall h h' n,
  h <> h' -> remove Z.eq_dec h (repeat h' n) = repeat h' n.
Proof.
  intros h h' n H1. induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. destruct (Z.eq_dec h h') as [H2 | H2]; try contradiction. rewrite IH. reflexivity.
Qed.

Lemma count_occ_remove_eq : forall h t,
  count_occ Z.eq_dec (remove Z.eq_dec h t) h = 0%nat.
Proof.
  intros h t. induction t as [| h' t' IH].
  - simpl. reflexivity.
  - simpl. destruct (Z.eq_dec h h') as [H1 | H1].
    + rewrite H1. simpl. destruct (Z.eq_dec h h) as [H2 | H2]; try lia. rewrite H1 in IH. apply IH.
    + simpl. destruct (Z.eq_dec h' h) as [H2 | H2]; try lia.
Qed.

Lemma count_occ_reduce_freq_to_half : forall l z,
  (Nat.div2 (count_occ Z.eq_dec l z) = count_occ Z.eq_dec (reduce_freq_to_half Z.eq_dec l) z)%nat.
Proof.
  intros l z. assert (In z l \/ ~In z l) as [H1 | H1] by apply classic.
  2 : { rewrite count_occ_reduce_freq_not_in; auto. apply (count_occ_not_In Z.eq_dec) in H1; auto. rewrite H1. reflexivity. }
  induction l as [| h t IH].
  - inversion H1.
  - destruct H1 as [H1 | H1].
    + rewrite H1. simpl. destruct (Z.eq_dec z z) as [H2 | H2]; try lia. simpl. rewrite count_occ_app. rewrite count_occ_repeat_eq.
      rewrite count_occ_remove_eq. lia.
    + pose proof H1 as H1'. apply IH in H1. destruct (Z.eq_dec h z) as [H2 | H2].
      * rewrite H2. simpl. destruct (Z.eq_dec z z) as [H3 | H3]; try lia. simpl. rewrite count_occ_app. rewrite count_occ_repeat_eq.
        rewrite count_occ_remove_eq. lia.
      * simpl. destruct (Z.eq_dec h z) as [H3 | H3]; destruct (Z.eq_dec h h) as [H4 | H4]; try lia.
        rewrite H1. simpl. rewrite count_occ_app. rewrite count_occ_repeat_neq; auto. rewrite count_occ_remove_neq; auto.
Qed.

Lemma count_occ_reduce_freq_by_factor : forall l z k,
  (count_occ Z.eq_dec l z / k = count_occ Z.eq_dec (reduce_freq_by_factor Z.eq_dec k l) z)%nat.
Proof.
  intros l z k. assert (In z l \/ ~In z l) as [H1 | H1] by apply classic.
  2 : { rewrite count_occ_reduce_freq_factor_not_in; auto. apply (count_occ_not_In Z.eq_dec) in H1; auto. rewrite H1. apply Nat.Div0.div_0_l. }
  induction l as [| h t IH].
  - inversion H1.
  - destruct H1 as [H1 | H1].
    + rewrite H1. simpl. destruct (Z.eq_dec z z) as [H2 | H2]; try lia. simpl. rewrite count_occ_app. rewrite count_occ_repeat_eq.
      rewrite count_occ_remove_eq. lia.
    + pose proof H1 as H1'. apply IH in H1. destruct (Z.eq_dec h z) as [H2 | H2].
      * rewrite H2. simpl. destruct (Z.eq_dec z z) as [H3 | H3]; try lia. simpl. rewrite count_occ_app. rewrite count_occ_repeat_eq.
        rewrite count_occ_remove_eq. lia.
      * simpl. destruct (Z.eq_dec h z) as [H3 | H3]; destruct (Z.eq_dec h h) as [H4 | H4]; try lia.
        rewrite H1. simpl. rewrite count_occ_app. rewrite count_occ_repeat_neq; auto. rewrite count_occ_remove_neq; auto.
Qed.

Lemma count_occ_reduce_freq_to_half_prime : forall l z,
  (count_occ Z.eq_dec l z / 2 = count_occ Z.eq_dec (reduce_freq_to_half Z.eq_dec l) z)%nat.
Proof.
  intros l z. pose proof (count_occ_reduce_freq_to_half l z) as H1. rewrite Nat.div2_div in H1. apply H1.
Qed.

Lemma count_occ_reduce_freq_by_factor_prime : forall l z k,
  (count_occ Z.eq_dec l z / k = count_occ Z.eq_dec (reduce_freq_by_factor Z.eq_dec k l) z)%nat.
Proof.
  intros l z k. pose proof (count_occ_reduce_freq_by_factor l z k) as H1. apply H1.
Qed.

Lemma count_occ_even_eq_app_reduce_freq_to_half : forall l1 l2,
  (forall z, Nat.Even (count_occ Z.eq_dec l1 z)) -> (l2 = reduce_freq_to_half Z.eq_dec l1) ->
  (forall z, (count_occ Z.eq_dec l1 z = count_occ Z.eq_dec (l2 ++ l2) z)%nat).
Proof.
  intros l1 l2 H1 H2 z. rewrite H2. rewrite count_occ_app. repeat rewrite <- count_occ_reduce_freq_to_half. 
  specialize (H1 z). destruct H1 as [n H1]. rewrite H1. rewrite div2_double. lia.
Qed.

Lemma count_occ_even_eq_app_reduce_freq_by_factor : forall l1 l2 k,
  (forall z, (exists q, (count_occ Z.eq_dec l1 z) = q * k)%nat) -> (l2 = reduce_freq_by_factor Z.eq_dec k l1) ->
  (forall z, (count_occ Z.eq_dec l1 z = count_occ Z.eq_dec (repeat_app l2 k) z)%nat).
Proof.
  intros l1 l2 k H1 H2 z. rewrite H2. rewrite count_occ_repeat_app. repeat rewrite <- count_occ_reduce_freq_by_factor. 
  specialize (H1 z). destruct H1 as [q H1]. rewrite H1. assert (k = 0 \/ k <> 0)%nat as [H3 | H3] by lia.
  - rewrite H3. simpl. lia.
  - rewrite Nat.div_mul; lia.
Qed.

Lemma fold_right_even_square : forall l1,
    (forall z, Nat.Even (count_occ Z.eq_dec l1 z)) -> exists l2,
    fold_right Z.mul 1 l1 = (fold_right Z.mul 1 l2)^2.
Proof.
  intros l1 H1. set (l2 := reduce_freq_to_half Z.eq_dec l1). exists (l2).
  pose proof (count_occ_even_eq_app_reduce_freq_to_half l1 l2 H1 eq_refl) as H2. 
  apply count_occ_equ_fold_right in H2. rewrite <- H2. rewrite fold_right_mult_app_Z. nia. 
Qed.

Lemma fold_right_factor : forall l1 k,
  (forall z, (exists q, (count_occ Z.eq_dec l1 z) = q * k)%nat) -> exists l2,
  fold_right Z.mul 1 l1 = (fold_right Z.mul 1 l2)^Z.of_nat k.
Proof.
  intros l1 k H1. set (l2 := reduce_freq_by_factor Z.eq_dec k l1). exists (l2).
  pose proof (count_occ_even_eq_app_reduce_freq_by_factor l1 l2 k H1 eq_refl) as H2. 
  apply count_occ_equ_fold_right in H2. rewrite <- H2. rewrite fold_right_mult_repeat_app_Z. reflexivity.
Qed.

Lemma even_count_occ_perfect_square : forall z,
  (exists l, z = fold_right Z.mul 1 l /\ (forall p, Nat.Even (count_occ Z.eq_dec l p))) ->
    (exists m, z = m^2).
Proof.
  intros z [l [H1 H2]]. pose proof (fold_right_even_square l H2) as H3.
  destruct H3 as [l2 H3]. exists (fold_right Z.mul 1 l2). rewrite H1. rewrite H3. reflexivity.
Qed.

Lemma count_occ_perfect_factor : forall z k,
  (exists l, z = fold_right Z.mul 1 l /\ (forall p, (exists q, (count_occ Z.eq_dec l p) = q * k)%nat)) ->
    (exists m, z = m^Z.of_nat k).
Proof.
  intros z k [l [H1 H2]]. pose proof (fold_right_factor l k H2) as H3.
  destruct H3 as [l2 H3]. exists (fold_right Z.mul 1 l2). rewrite H1. rewrite H3. reflexivity.
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

Open Scope R_scope.

Lemma Rpower_gt_0 : forall r n,
  r > 0 -> Rpower r n > 0.
Proof.
  intros r n H1. unfold Rpower. destruct (Rle_dec 0 r).
  - apply exp_pos.
  - apply exp_pos.
Qed.

Lemma Rpow_neq_0 : forall r n,
  r <> 0 -> r ^ n <> 0.
Proof.
  intros r n H1. induction n as [| n' IH].
  - simpl. nra.
  - simpl. nra.
Qed.

Lemma Rpow_div_l : forall r1 r2 k,
  r2 <> 0 -> r2 <> 0 -> (r1 / r2) ^ k = r1 ^ k / r2 ^ k.
Proof.
  intros r1 r2 k H1 H2. induction k as [| k' IH].
  - simpl. field.
  - simpl. rewrite IH. field. split. 2 : { nra. }
    apply Rpow_neq_0. auto.
Qed.

Lemma Rpow_1_k : forall k,
  1 ^ k = 1.
Proof.
  intros k. induction k as [| k' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. lra.
Qed.

Lemma pow_neg1_n_plus_1 : forall (n : nat),
  (-1) ^ (n + 1) = (-1) ^ n * (-1) ^ 1.
Proof.
  intros n.
  induction n.
  - simpl. lra.
  - simpl. rewrite IHn. lra.
Qed.

Lemma pow_neg1_n_plus_n : forall (n : nat),
  (-1)^(n+n) = (-1)^n * (-1)^n.
Proof.
  induction n as [| k IH].
  - simpl. lra.
  - replace ((-1)^(S k)) with ((-1)^k * (-1)^1) by ((simpl; lra)).
    replace ((-1)^1) with (-1) by lra.
    replace ((-1) ^ k * -1 * ((-1) ^ k * -1)) with ((-1) ^ k * (-1) ^ k) by lra.
    rewrite <- IH.
    replace ((S k + S k))%nat with (((k + k) + 1) + 1)%nat by lia.
    repeat rewrite pow_neg1_n_plus_1. lra. 
Qed.

Lemma pow_neg1_n : forall (n : nat),
  (-1)^n = 1 \/ (-1)^n = -1.
Proof.
  intros n.
  induction n as [| k IH].
  - simpl. left. lra.
  - destruct IH as [H | H].
    + right. replace (S k) with (k + 1)%nat by lia. rewrite pow_neg1_n_plus_1. rewrite H. lra.
    + left. replace (S k) with (k + 1)%nat by lia. rewrite pow_neg1_n_plus_1. rewrite H. lra.
Qed.

Lemma r_mult_r_is_Rsqr : forall r : R, r * r = Rsqr r.
Proof.
  intros r.
  unfold Rsqr. reflexivity.
Qed.

Lemma pow_neg1_odd : forall k, Nat.Odd k -> (-1) ^ k = -1.
Proof.
  intros k Hodd.
  destruct Hodd as [m Heq]. rewrite Heq.
  rewrite pow_neg1_n_plus_1. simpl.
  replace ((m + (m + 0))%nat) with (m + m)%nat by lia.
  rewrite Rmult_1_r. rewrite pow_neg1_n_plus_n. 
  rewrite r_mult_r_is_Rsqr. assert (H : (0 <= ((-1) ^ m)²)) by apply Rle_0_sqr.
  destruct (pow_neg1_n m) as [Hpos | Hneg].
  - rewrite Hpos. unfold Rsqr. lra.
  - rewrite Hneg. unfold Rsqr. lra.
Qed.

Lemma pow_neg1_even : forall k, Nat.Even k -> (-1) ^ k = 1.
Proof.
  intros k. unfold Nat.Even. intros [m Heq].
  assert (H2: (-1) ^ (2 * m + 1) = -1).
  { apply pow_neg1_odd. exists m. reflexivity. } 
  rewrite Heq. rewrite pow_neg1_n_plus_1 in H2. lra.
Qed.

Lemma mult_IZR_eq_1 : forall z1 z2,
  IZR z1 * IZR z2 = 1 -> ((z1 = 1 /\ z2 = 1) \/ (z1 = -1 /\ z2 = -1))%Z.
Proof.
  intros z1 z2 H1. assert (z1 = 0 \/ z1 = 1 \/ z1 = -1 \/ z1 < -1 \/ z1 > 1)%Z as [H2 | [H2 | [H2 | [H2 | H2]]]] by lia.
  - rewrite H2 in H1. lra.
  - rewrite H2 in H1. rewrite Rmult_1_l in H1. apply eq_IZR in H1. lia.
  - rewrite H2 in H1. simpl in H1. assert (IZR z2 = -1) as H3 by lra. apply eq_IZR in H3. lia.
  - rewrite <- mult_IZR in H1. apply eq_IZR in H1. pose proof Ztrichotomy z2 0 as [H3 | [H3 | H3]]; lia.
  - rewrite <- mult_IZR in H1. apply eq_IZR in H1. pose proof Ztrichotomy z2 0 as [H3 | [H3 | H3]]; lia.
Qed.

Lemma mult_IZR_eq_neg1 : forall z1 z2,
  IZR z1 * IZR z2 = -1 -> ((z1 = 1 /\ z2 = -1) \/ (z1 = -1 /\ z2 = 1))%Z.
Proof.
  intros z1 z2 H1. assert (z1 = 0 \/ z1 = 1 \/ z1 = -1 \/ z1 < -1 \/ z1 > 1)%Z as [H2 | [H2 | [H2 | [H2 | H2]]]] by lia.
  - rewrite H2 in H1. lra.
  - rewrite H2 in H1. rewrite Rmult_1_l in H1. apply eq_IZR in H1. lia.
  - rewrite H2 in H1. simpl in H1. assert (IZR z2 = 1) as H3 by lra. apply eq_IZR in H3. lia.
  - rewrite <- mult_IZR in H1. apply eq_IZR in H1. pose proof Ztrichotomy z2 0 as [H3 | [H3 | H3]]; lia.
  - rewrite <- mult_IZR in H1. apply eq_IZR in H1. pose proof Ztrichotomy z2 0 as [H3 | [H3 | H3]]; lia.
Qed.

Close Scope R_scope.

Lemma Zmult_eq_1 : forall z1 z2,
  z1 * z2 = 1 -> ((z1 = 1 /\ z2 = 1) \/ (z1 = -1 /\ z2 = -1))%Z.
Proof.
  intros z1 z2 H1. pose proof Ztrichotomy z1 0 as [H2 | [H2 | H2]]; pose proof Ztrichotomy z2 0 as [H3 | [H3 | H3]]; lia.
Qed.

Lemma Zmult_eq_neg1 : forall z1 z2,
  z1 * z2 = -1 -> ((z1 = 1 /\ z2 = -1) \/ (z1 = -1 /\ z2 = 1))%Z.
Proof.
  intros z1 z2 H1. pose proof Ztrichotomy z1 0 as [H2 | [H2 | H2]]; pose proof Ztrichotomy z2 0 as [H3 | [H3 | H3]]; lia.
Qed.

Lemma Even_ZEven : forall n,
  Nat.Even n <-> Z.Even (Z.of_nat n).
Proof.
  intros n; split.
  - intros [m H1]. exists (Z.of_nat m). lia.
  - intros [m H1]. exists (Z.to_nat m). lia.
Qed.

Lemma Odd_ZOdd : forall n,
  Nat.Odd n <-> Z.Odd (Z.of_nat n).
Proof.
  intros n; split.
  - intros [m H1]. exists (Z.of_nat m). lia.
  - intros [m H1]. exists (Z.to_nat m). lia.
Qed.


Lemma Zpow_neg1_nat_even : forall n : nat,
  Nat.Even n -> (-1) ^ (Z.of_nat n) = 1.
Proof.
  intros n H1. apply Even_ZEven in H1. rewrite <- Z.pow_opp_even. simpl. rewrite Z.pow_1_l; lia. auto.
Qed.

Lemma Zpow_neg1_nat_odd : forall n : nat,
  Nat.Odd n -> (-1) ^ (Z.of_nat n) = -1.
Proof.
  intros n H1. apply Odd_ZOdd in H1. rewrite Z.pow_opp_odd with (a := 1). rewrite Z.pow_1_l; lia. auto.
Qed.

Lemma Zpow_neg_nat_odd : forall n z ,
  Nat.Odd n -> (-z) ^ (Z.of_nat n) = -z ^ (Z.of_nat n).
Proof.
  intros n z H1. apply Odd_ZOdd in H1. rewrite Z.pow_opp_odd with (a := z). reflexivity. auto.
Qed.

Lemma Zpow_neg_nat_even : forall n z,
  Nat.Even n -> (-z) ^ (Z.of_nat n) = z ^ (Z.of_nat n).
Proof.
  intros n z H1. apply Even_ZEven in H1. rewrite Z.pow_opp_even. reflexivity. auto.
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

Lemma not_perfect_square : forall z : Z,
  (exists z2, z > z2^2 /\ z < (z2+1)^2) -> ~(exists m, (z = m^2)%Z).
Proof.
  intros z H1. intros [m H2]. destruct H1 as [z2 [H3 H4]]. rewrite H2 in *. clear H2.
  destruct (Ztrichotomy m 0) as [H5 | [H5 | H5]]; destruct (Ztrichotomy z2 0) as [H6 | [H6  | H6]]; try lia.
  - assert (-m > z2) by nia. assert (-m < z2 + 1) by nia. nia.
  - assert (m > z2) by nia. assert (m < z2 + 1) by nia. nia.
Qed.

Lemma sqrt_2_irrational_prime : irrational (sqrt 2).
Proof.
  apply lemma_2_17_b; try lia. intros [m H1]. assert (H2 : exists z, 2 > z^2 /\ 2 < (z+1)^2) by (exists 1; lia).
  pose proof (not_perfect_square 2 H2) as H3. apply H3. exists m. apply H1.
Qed.

Lemma first_n_primes_prime_list : forall l,
  first_n_primes l -> prime_list l.
Proof.
  intros l [H1 [H2 H3]]. apply H2. 
Qed.

Lemma lemma_2_17_d : forall (l : list Z),
  first_n_primes l -> exists p : Z, Znt.prime' p /\ p > max_list_Z l.
Proof.
  intros l [H1 [H2 H3]]. set (N := fold_right Z.mul 1 l + 1).
  assert (N > 1) as H4 by (destruct l; apply prime_list_product_gt_1 in H2; lia).
  destruct (prime_divides N H4) as [q H5]. exists q. split.
  - apply H5.
  - destruct H5 as [H5 H6]. destruct (in_dec Z.eq_dec q l) as [H7 | H7].
    -- assert ((q | fold_right Z.mul 1 l)) as H8 by (apply fold_right_factor_divides; auto).
       unfold N in H6. pose proof (prime_no_div q (fold_right Z.mul 1 l) H5 H8 H6) as H9. lia.
    -- specialize (H3 q). tauto.
Qed.

(* we know that for every prime list there exists a prime p which is larger than every prime in the prime list
   we prove that a prime list exists of length 0(base case) suppose one exists of length k
   then we show that one exists of length S k. but how to find the next prime? we don't know where it might be
   but we know by the prior lemma that a larger one exists. then we just form a set of all the primes larger than
   max of our list this bounded below non-empty set and so has a least element. we can grab this element with well-ordering
   principle and use it to construct S k. BOO Ya!*)

Lemma gt_list_max_not_in : forall l x,
  (x > max_list_Z l)%Z -> ~(In x l).
Proof.
  intros l x H1 H2. induction l as [| h t IH].
  - inversion H2.
  - simpl in H1. simpl in H2. destruct H2 as [H2 | H2].
    -- rewrite H2 in H1. lia.
    -- apply IH in H2. lia. lia.
Qed.

Lemma le_max_list_Z : forall l x z,
  x <= max_list_Z (z :: l) -> x = z \/ (x < z /\ x > max_list_Z l) \/ x <= max_list_Z l.
Proof.
  intros l x z H1. induction l as [| h l' IH].
  - simpl in *. assert (H2 : z <= 0 \/ z > 0) by lia. destruct H2.
    -- lia.
    -- lia.
  - simpl in *. assert (H2 : z <= h \/ z > h) by lia. destruct H2.
    -- simpl in H1. lia.
    -- simpl in H1. lia.
Qed.

Lemma prime_list_len : forall n,
  exists l, first_n_primes l /\ length l = n.
Proof.
  intros n. induction n as [| k IH].
  - exists []. split.
    -- repeat split; repeat constructor. intros x [H1 H2]. simpl in H2.
       rewrite -> Znt.prime_alt in H1. assert (H3 : x >= 2) by (apply Znt.prime_ge_2 in H1; lia). lia.
    -- simpl. reflexivity.
  - destruct IH as [l [H1 H2]]. destruct (lemma_2_17_d l H1) as [p [H3 H4]].
    set (E := (fun x => (Znt.prime' x /\ x > max_list_Z l)%Z)).
    assert (exists p, E p) as [p' H5]. { exists p. unfold E. split. apply H3. apply H4. }
    assert (H6 : forall z, E z -> z >= 0).
    { intros z [H6 H7]. assert (z >= 2). {rewrite Znt.prime_alt in H6. apply Znt.prime_ge_2 in H6. lia. } lia. }
    assert (H7 : exists z, E z). { exists p'. apply H5. }
    pose proof (well_ordering_Z E H6 H7) as [z [[H8 H9] H10]].
    exists (z :: l). split.
    -- repeat split.
      + constructor. apply gt_list_max_not_in. lia. unfold first_n_primes in H1. tauto.
      + unfold prime_list. unfold first_n_primes in H1; apply Forall_cons; tauto.
      + intros x [H11 H12]. simpl. apply le_max_list_Z in H12 as [H12 | [H12 | H12]].
        * lia.
        * destruct H12 as [H12 H13]. specialize (H10 x). assert (x >= 0) as H14.
          { rewrite Znt.prime_alt in H11. apply Znt.prime_ge_2 in H11. lia. }
          assert (E x) as H15. { unfold E. split. apply H11. apply H13. }
          apply H10 in H15. 2 : { apply H14. } lia.
        * right. apply H1. split. apply H11. apply H12.
    -- simpl. lia.
Qed.

Lemma list_len_cons : forall {A : Type} h (l : list A),
  length (h :: l) = S (length l).
Proof.
  intros A h l. simpl. reflexivity.
Qed.

Lemma max_list_cons : forall l h m,
  m = max_list_Z (h :: l) -> m = h \/ m = max_list_Z l.
Proof.
  intros l h m H. induction l as [| h' l' IH]; simpl in *; lia.
Qed.

Lemma max_list_cons_ge : forall l h m,
  m >= max_list_Z (h :: l) -> m >= h /\ m >= max_list_Z l.
Proof.
  intros l h m H. induction l as [| h' l' IH].
  - simpl in *. lia.
  - simpl in *. assert (m >= h /\ m >= max_list_Z l') as [H1 H2] by lia. split.
    -- lia.
    -- lia.
Qed.

Lemma max_list_ge_not_in : forall l h,
  h > 0 -> h >= max_list_Z l /\ ~ In h l -> h > max_list_Z l.
Proof.
  intros l h H1 [H2 H3]. induction l as [| h' l' IH].
  - simpl. lia.
  - simpl. assert (~ In h l') as H4. { pose proof in_cons h' h l' as H4. tauto. }
    assert (h >= max_list_Z l') as H5. { apply max_list_cons_ge in H2 as [H2 H6]. apply IH in H4 as H7. lia. lia. }
    assert (H6 : h > max_list_Z l'). { apply IH in H4 as H6. lia. lia. }
    assert (H7 : h <> h'). { intros H7. rewrite H7 in H3. assert (In h' (h' :: l')) as H8 by apply in_eq. tauto. }
    pose proof (max_list_cons_ge l' h' h) as [H8 H9]. lia. lia.
Qed.

Lemma max_list_ge_not_in' : forall l h,
  max_list_Z l > 0 -> max_list_Z l >= h /\ ~ In h l -> max_list_Z l > h.
Proof.
  intros l h H1 [H2 H3]. induction l as [| h' l' IH].
  - simpl in *. lia.
  - simpl. assert (~ In h l') as H4. { pose proof in_cons h' h l' as H4. tauto. }
    assert (max_list_Z (h' :: l') = h' \/ max_list_Z (h' :: l') = max_list_Z l') as [H5 | H5] by (simpl; lia).
    -- rewrite H5 in H2. assert (h' <> h) as H6.
       { intros H6. rewrite H6 in H3. assert (In h' (h' :: l')) as H7 by apply in_eq. rewrite H6 in H7. tauto. } lia.
    -- assert (max_list_Z l' >= h) as H6. { rewrite H5 in H2. tauto. }
       assert (max_list_Z l' > h) as H7. { apply IH in H4 as H7; lia; auto. }
       lia.
Qed.

Lemma max_list_Z_eq : forall l h,
  max_list_Z (h :: l) = h \/ max_list_Z (h :: l) = max_list_Z l.
Proof.
  intros l h. simpl. lia.
Qed.

Theorem list_has_len : forall (l : list Z) (a : Z),
  In a l -> (length l > 0)%nat.
Proof.
  intros l a. induction l as [| h l' IH].
  - simpl. lia.
  - simpl. intros [H1 | H1]; lia.
Qed.

Lemma remove_one_len : forall l x,
  In x l -> length (remove_one Z.eq_dec x l) = (length l - 1)%nat.
Proof.
  intros l x H. induction l as [| h l' IH].
  - inversion H.
  - simpl. destruct (Z.eq_dec h x) as [H1 | H1].
    -- lia.
    -- simpl. destruct H as [H | H]. lia. rewrite IH.
       --- assert (length l' > 0)%nat as H2. { apply list_has_len with (a := x). apply H. } lia.
       --- apply H.
Qed.

Lemma remove_one_remains : forall l x1 x2,
  In x1 l -> x1 <> x2 -> In x1 (remove_one Z.eq_dec x2 l).
Proof.
  intros l x1 x2 H. induction l as [| h l' IH].
  - inversion H.
  - simpl. intros H1. destruct (Z.eq_dec h x2) as [H2 | H2].
    -- simpl in H. destruct H as [H | H].
       --- lia.
       --- tauto.
    -- simpl. simpl in H. tauto.
Qed.

Lemma in_notin_neq : forall (l : list Z) x1 x2,
  In x1 l -> ~ (In x2 l) -> x1 <> x2.
Proof.
  intros l x1 x2 H1 H2. induction l as [| h l' IH].
  - inversion H1.
  - simpl in *. destruct H1 as [H1 | H1].
    -- rewrite H1 in H2. tauto.
    -- tauto.
Qed.

Theorem longer_list:
    forall l1 l2 : list Z,
    (forall x : Z, In x l1 -> In x l2) ->
    (exists x : Z, In x l2 /\ ~ In x l1) ->
    NoDup l1 ->
    (length l2 > length l1)%nat.
  Proof.
    intros l1 l2 H1 H2 H3. generalize dependent l2.
    induction l1 as [| h l1' IH].
    - intros l2 H4 H5. simpl in *. destruct H5 as [x H5]. assert (exists a, In a l2) as [a H6].
    { exists x. apply H5. } apply list_has_len in H6. lia.
    - intros l2 H4 [a [H5 H6]]. apply NoDup_cons_iff in H3. destruct H3 as [H3 H3'].
      specialize (IH H3' (remove_one Z.eq_dec a l2)). apply not_in_cons in H6 as [H6 H6'].
      assert (In h (remove_one Z.eq_dec a l2)) as H7.
      { apply remove_one_remains. apply (H4 h). simpl. lia. lia. }
      assert (length (remove_one Z.eq_dec a l2) > length l1')%nat as H8.
      { apply IH. intros x H8. apply remove_one_remains. apply (H4 x). simpl. tauto. 2 : { exists h. tauto. }  apply in_notin_neq with (l := l1') (x2 := a). apply H8. apply H6'. }
      rewrite remove_one_len in H8. simpl. lia. tauto.
  Qed.

Theorem pigeonhole_principle_Z : forall (l1 l2 : list Z),
  (forall x, In x l1 -> In x l2) -> (length l2 < length l1)%nat ->
    ~ NoDup l1.
Proof.
  intros l1. induction l1 as [|a l1' IH].
  - simpl. lia.
  - simpl. intros l2 H1 H2. destruct (in_dec Z.eq_dec a (l1')) as [H3 | H3].
    -- intros H4. apply NoDup_cons_iff in H4 as [H4 H5]. tauto.
    -- intros H4. apply IH with (l2 := l2).
       3 : { apply NoDup_cons_iff in H4. tauto. }
       intros x H5. specialize (H1 x). assert (a = x \/ In x l1') as H6 by tauto. tauto.
       assert (H5 : (length l2 > length l1')%nat).
       { apply longer_list. intros x H5. apply (H1 x). tauto. exists a. split. apply (H1 a).
        tauto. tauto. apply NoDup_cons_iff in H4. tauto. }
       lia.
Qed.

Definition Zseq_pos (seq : list nat) : list Z :=
  map Z.of_nat (seq).

Lemma in_Zseq_pos : forall start len x,
  let l := seq start len in
    x > 0 -> In (Z.to_nat x) (seq start len) -> In x (Zseq_pos l).
Proof.
  intros start len x l H. unfold Zseq_pos.
  rewrite in_map_iff. exists (Z.to_nat x). split. lia. auto.
Qed.

Lemma Zseq_len : forall start len,
  let l := seq start len in
    length (l) = length (Zseq_pos l).
Proof.
  intros start len. unfold Zseq_pos. rewrite map_length. reflexivity.
Qed.

Lemma in_list_1 : forall l,
  Z.of_nat (length l) > 0 -> NoDup l -> Forall (fun x => x > 0) l -> Z.of_nat (length l) = max_list_Z l -> In 1 l.
Proof.
  intros l H1 H2 H3 H4. destruct (in_dec Z.eq_dec 1 l) as [H5 | H5]. apply H5.
  set (l2 := Zseq_pos (seq 2 (Z.to_nat (max_list_Z l - 1)))). assert (~NoDup l) as H6.
  - apply pigeonhole_principle_Z with (l2 := l2).
    2 : { assert (length l2 = Z.to_nat (max_list_Z l) - 1)%nat. { unfold l2. rewrite <- Zseq_len. rewrite seq_length. lia. } lia. }
    intros x H6. apply in_Zseq_pos. rewrite Forall_forall in H3. specialize (H3 x). tauto. apply in_seq.
    replace (2 + Z.to_nat (max_list_Z l - 1))%nat with (Z.to_nat (max_list_Z l) + 1)%nat by lia. pose proof H6 as H6'. pose proof H6 as H6''.
    apply in_list_le_max in H6. rewrite Forall_forall in H3. specialize (H3 x). apply H3 in H6'. assert (~x = 1). unfold not in *. intros H7. apply H5. rewrite H7 in H6''. tauto.
    lia.
  - tauto.
Qed.

Lemma list_len_lt_max : forall l,
  Forall (fun x => x > 1) l /\ NoDup l -> Z.of_nat (length l) <= max_list_Z l.
Proof.
  intros l. induction l as [| h l' IH].
  - intros [H1 H2]. simpl. lia.
  - intros [H1 H2]. apply Forall_cons_iff in H1 as [H1 H1']. apply NoDup_cons_iff in H2 as [H2 H3].
    assert (Z.of_nat(length l') <= max_list_Z l') as H4 by (apply IH; split; auto).
    rewrite list_len_cons. assert (max_list_Z (h :: l') = h \/ max_list_Z (h :: l') = max_list_Z l') as [H5 | H5] by (simpl; lia).
    -- rewrite H5. assert (H6 : h >= max_list_Z l') by (induction l'; simpl in *; lia).
       pose proof (max_list_ge_not_in l' h) as H7. assert (H8 : h > 0) by lia. apply H7 in H8. lia. auto.
    -- rewrite H5. assert (H6 : max_list_Z l' >= h) by (induction l'; simpl in *; lia).
       pose proof (max_list_ge_not_in' l' h) as H7. assert (H8 : max_list_Z l' > 0) by lia. apply H7 in H8. 2 : { tauto. }
       assert (Z.of_nat (length l') = max_list_Z l' \/ Z.of_nat (length l') < max_list_Z l') as [H9 | H9].
       --- lia.
       --- rewrite <- H5 in H9. assert (NoDup (h :: l')) as H10 by (apply NoDup_cons; auto).
           assert (Z.of_nat (length l') = max_list_Z l' \/ Z.of_nat (length l') < max_list_Z l') as [H11 | H11] by lia.
           2 : { lia. } apply in_list_1 in H11.
           + rewrite Forall_forall in H1'. specialize (H1' 1). apply H1' in H11. lia.
           + lia.
           + apply H3.
           + assert (H12 : Forall (fun x : Z => x > 1) l' -> Forall (fun x : Z => x > 0) l').
             { intros H12. rewrite Forall_forall in H12. rewrite Forall_forall. intros x H13. apply H12 in H13. lia. }
             tauto.
      --- lia.
Qed.

Lemma max_primes_ge_len : forall l,
  first_n_primes l -> max_list_Z l >= Z.of_nat (length l).
Proof.
  intros l H1. pose proof Znt.prime_ge_2 as H2.
  pose proof (Znt.not_prime_1) as H3. assert (H4 : ~ In 1 l).
  { intros H4. unfold first_n_primes in H1. destruct H1 as [H1 [H5 H6]]. unfold prime_list in H5.
    rewrite Forall_forall in H5. specialize (H5 1). apply H5 in H4. rewrite Znt.prime_alt in H4. tauto. }
  unfold first_n_primes in H1. destruct H1 as [H1 [H5 H6]]. unfold prime_list in H5. rewrite Forall_forall in H5.
  apply Z.le_ge. apply list_len_lt_max. split. rewrite Forall_forall. intros x H7. specialize (H5 x). apply H5 in H7.
  apply Znt.prime_alt in H7. apply Znt.prime_ge_2 in H7. lia. apply H1.
Qed.

Lemma prime_in_first_n_primes : forall p,
  Znt.prime' p -> exists l, first_n_primes l /\ In p l.
Proof.
  intros p H1. pose proof (prime_list_len (Z.to_nat p)) as [l [H2 H3]].
  exists l. split.
  - apply H2.
  - apply H2. apply max_primes_ge_len in H2. rewrite H3 in H2. rewrite Z2Nat.id in H2.
    2 : { rewrite Znt.prime_alt in H1. apply Znt.prime_ge_2 in H1. lia. }
    split. apply H1. lia.
Qed.

Lemma gt_max_gt_all : forall (l : list Z) x1 x2,
  In x1 l -> x2 > max_list_Z l -> x2 > x1.
Proof.
  intros l x1 x2 H1 H2. induction l as [| h l' IH].
  - inversion H1.
  - simpl in H1. simpl in H2. destruct H1 as [H1 | H1].
    -- lia.
    -- apply IH. apply H1. lia.
Qed.

Theorem inf_primes : forall p1,
  Znt.prime p1 -> exists p2, Znt.prime p2 /\ p2 > p1.
Proof.
  intros p1 H1. rewrite <- Znt.prime_alt in H1. 
  apply prime_in_first_n_primes in H1 as [l [H1 H2]].
  pose proof (lemma_2_17_d l H1) as [p2 [H3 H4]]. exists p2. split.
  - rewrite Znt.prime_alt in H3. apply H3.
  - apply gt_max_gt_all with (l := l); tauto.
Qed.

Close Scope Z_scope.

Open Scope R_scope.

Definition integer (x : R) : Prop :=
  exists n : Z, x = IZR n.

Lemma pow_sub : forall (x:R) (n m:nat), x <> 0 -> (n >= m)%nat -> x ^ (n - m) = x ^ n / x ^ m.
Proof.
  intros x n m H1 H2. induction m as [| k IH].
  - simpl. rewrite Nat.sub_0_r. lra.
  - assert (n = S k \/ n >= k)%nat as [H3 | H3] by lia.
    -- rewrite H3. replace (S k - S k)%nat with 0%nat by lia. rewrite pow_O. field. apply pow_nonzero; auto.
    -- apply Rmult_eq_reg_l with (r := x); auto. replace x with (x^1) at 1 by lra. rewrite <- pow_add. replace (1 + (n - S k))%nat with (n - k)%nat by lia.
        rewrite IH; try lia. simpl. field. split; auto. apply pow_nonzero; auto.
Qed.

Lemma div_nonzero: forall x y : R, x <> 0 -> y <> 0 -> x / y <> 0.
Proof.
  intros x y Hx Hy.
  unfold Rdiv.
  apply Rmult_integral_contrapositive_currified; auto.
  apply Rinv_neq_0_compat; auto.
Qed.

Lemma sum_divides_Z : forall a b c : Z,
  (c <> 0)%Z -> (a + b = 0)%Z -> (c | a)%Z -> (c | b)%Z.
Proof.
  intros a b c H1 H2 [d H3]. exists (-a / c)%Z. assert (H4 : (a = -b)%Z) by lia. rewrite Z.mul_comm. rewrite z_mul_div. rewrite Z_div_mult_good. lia. 
  3 : { exists (-d)%Z. lia. } lia. lia.
Qed.

Definition R_divides (r1 r2 : R) : Prop :=
  exists a b : Z, r1 = IZR a /\ r2 = IZR b /\ (a | b)%Z.

Notation "( x | y )" := (R_divides x y) (at level 0) : R_scope.

Lemma R_divides_refl : (3 | 6)%R.
Proof.
  exists (3%Z), (6%Z); repeat split; try reflexivity. exists 2%Z. reflexivity.
Qed.

Lemma R_divides_plus : forall r r1 r2,
  (r | r1) -> (r | r2) -> (r | (r1 + r2)).
Proof.
  intros r r1 r2 [a [b [H1 [H2 [c H3]]]]] [e [f [H4 [H5 [g H6]]]]]. exists (a%Z), (b + f)%Z. repeat split; auto.
  - rewrite plus_IZR. lra.
  - exists (c + g)%Z. rewrite H3. rewrite H6. apply eq_IZR. rewrite plus_IZR. repeat rewrite mult_IZR. rewrite plus_IZR.
    apply IZR_eq in H6, H3. rewrite mult_IZR in H3, H6. nra. 
Qed.

Lemma R_divides_sum : forall i n (f : nat -> R) (r : R),
  (i <= n)%nat -> (forall j, (i <= j <= n)%nat -> (r | f j)) -> (r | sum_f i n f).
Proof.
  intros i n f r H1 H2. induction n as [| k IH].
  - assert (i = 0)%nat as H5 by lia. rewrite H5. rewrite sum_f_0_0. specialize (H2 0%nat). auto.
  - assert (i = S k \/ i = k \/ i < k)%nat as [H3 | [H3 | H3]] by lia.
    -- rewrite H3. rewrite sum_f_n_n. specialize (H2 (S k)). auto.
    -- rewrite sum_f_i_Sn_f; try lia. apply R_divides_plus; auto. apply IH; try lia. intros j H4. apply H2. lia.
    -- rewrite sum_f_i_Sn_f; try lia. apply R_divides_plus; auto. apply IH; try lia. intros j H4. apply H2. lia.
Qed.

Lemma IZR_divides : forall a b,
  (a | b)%Z <-> (IZR a | IZR b).
Proof.
  intros a b. split.
  - exists a, b. repeat split; auto.
  - intros [c [d [H1 [H2 H3]]]]. apply eq_IZR in H1, H2. rewrite H1, H2. auto.
Qed.

Lemma divides_neg_R : forall r1 r2,
  (r1 | r2) -> (r1 | -r2).
Proof.
  intros r1 r2 [a [b [H1 [H2 H3]]]]. rewrite H1, H2. rewrite <- opp_IZR. apply IZR_divides. apply Z.divide_opp_r. auto.
Qed.

Lemma prime_div_pow_div_Z : forall p a n,
  Znt.prime p -> (p | a ^ Z.of_nat n)%Z -> (p | a)%Z.
Proof.
  intros p a n H1 H2. induction n as [| k IH].
  - simpl in H2. destruct H2 as [b H2]. apply Znt.prime_alt in H1 as [H1 H1']. assert (b = 1)%Z as H3 by lia. lia.
  - replace (Z.of_nat (S k)) with (Z.succ (Z.of_nat k)) in H2 by lia. rewrite Z.pow_succ_r in H2; try lia. apply Znt.prime_mult in H2 as [H2 | H2]; auto.
Qed.

Lemma lemma_2_18_a : forall (x : R) (l : list Z),
  (sum_f 0 (length l) (fun i => IZR (nth i l 1%Z) * x ^ i) = 0) -> (irrational x \/ integer x).
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

(* TODO -- I still need to do 21, 22a, 26, 27, 28*)

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

Lemma pow_incrst_1 : forall r1 r2 n,
  (n > 0)%nat -> r1 > 0 -> r2 > 0 -> r1 < r2 -> r1^n < r2^n.
Proof.
  intros r1 r2 n H1 H2 H3 H4. generalize dependent r1. generalize dependent r2. induction n as [| k IH].
  - lia.
  - intros r2 H2 r1 H3 H4. simpl. destruct k; try nra. assert (H6 : r1^(S k) < r2 ^(S k)). { apply IH; try lia; try nra. }
    apply Rmult_gt_0_lt_compat; try nra. simpl. assert (r1 ^ k > 0). { apply pow_lt; nra. } nra. 
Qed.

Lemma pow_incrst_0 : forall r1 r2 n,
  r1 > 0 -> r2 > 0 -> r1^n < r2^n -> r1 < r2.
Proof.
  intros r1 r2 n H1 H2 H3. generalize dependent r1. generalize dependent r2. induction n as [| k IH].
  - intros r2 H1 r1 H2 H3. simpl in H3. lra.
  - intros r2 H1 r1 H2 H3. assert (k = 0 \/ k > 0)%nat as [H4 | H4] by lia.
    -- rewrite H4 in H3. simpl in H3. lra.
    -- simpl in H3. pose proof (Rtotal_order r1 r2) as [H5 | [H5 | H5]]; try nra.
       + rewrite H5 in H3. nra.
       + pose proof (pow_incrst_1 r2 r1 k H4 H1 H2) as H6. apply Rgt_lt in H5. specialize (H6 H5). assert (r1 ^ k > 0). { apply pow_lt; nra. } nra.
Qed.

Lemma pow_incrst_2 : forall r1 r2 n,
  r1 > 0 -> r2 > 0 -> r1 < r2 -> r1 ^ n <= r2 ^ n.
Proof.
  intros. assert (n = 0 \/ n <> 0)%nat as [H3 | H3] by lia.
  - rewrite H3. simpl. lra.
  - apply Rlt_le. apply pow_incrst_1 with (n := n); auto; try lia.
Qed.

Lemma pow_incrst_3 : forall r1 r2 n,
  (n > 0)%nat -> r1 > 0 -> r2 > 0 -> r1 ^ n <= r2 ^ n -> r1 <= r2.
Proof.
  intros r1 r2 n H1 H2 H3 H4. generalize dependent r1. generalize dependent r2. induction n as [| k IH].
  - intros r2 H2 r1 H3 H4. lia.
  - intros r2 H2 r1 H3 H4. assert (k = 0 \/ k > 0)%nat as [H5 | H5] by lia.
    -- rewrite H5 in H4. simpl in H4. lra.
    -- simpl in H4. pose proof (Rtotal_order r1 r2) as [H6 | [H6 | H6]]; try nra.
       pose proof (pow_incrst_2 r2 r1 k H2 H3 H6). apply IH; auto. assert (r1 ^ k > 0). { apply pow_lt; nra. } nra.
Qed.

Lemma pow_eq_1 : forall r1 r2 n,
  (n > 0)%nat -> r1 > 0 -> r2 > 0 -> r1 ^ n = r2 ^ n -> r1 = r2.
Proof.
  intros r1 r2 n H1 H2 H3 H4. generalize dependent r1. generalize dependent r2. induction n as [| k IH].
  - intros r2 H2 r1 H3 H4. lia.
  - intros r2 H2 r1 H3 H4. assert (k = 0 \/ k > 0)%nat as [H5 | H5] by lia.
    -- rewrite H5 in H4. simpl in H4. lra.
    -- pose proof (Rtotal_order r1 r2) as [H6 | [H6 | H6]]; auto.
       + apply pow_incrst_1 with (n := S k) in H6; auto; nra.
       + apply pow_incrst_1 with (n := S k) in H6; auto; nra.
Qed.

Lemma sqrt_2_weak_bound : 1.4 < sqrt 2 < 1.5.
Proof.
   split; (apply Rsqr_incrst_0; try lra; unfold Rsqr; repeat rewrite sqrt_sqrt; try lra; apply sqrt_pos).
Qed.

Lemma cbrt_2_weak_bound : 1.2 < Rpower 2 (1/3) < 1.3.
Proof.
  split; apply pow_incrst_0 with (n := 3%nat); try nra; try apply Rpower_gt_0; try lra; simpl; repeat rewrite Rmult_1_r; repeat rewrite <- Rpower_plus;
  replace (1 / 3 + (1 / 3 + 1 / 3)) with (INR 1); try rewrite Rpower_1; try nra; try nra; simpl; nra.
Qed.

Lemma not_integer : forall r n,
  IZR n < r < IZR (n + 1) -> ~ integer r.
Proof.
  intros r n [H1 H2] [m H3]. rewrite H3 in H1, H2. apply lt_IZR in H1, H2. lia.
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

Lemma Rpow_lt_1 : forall r n,
  0 < r < 1 -> (n > 0)%nat -> r ^ n < 1.
Proof.
  intros r n [H1 H2] H3. induction n as [| k IH].
  - lia.
  - simpl. destruct k.
    -- simpl. lra.
    -- assert (r ^ S k < 1) by (apply IH; lia). nra.
Qed.

Lemma Rpow_gt_1 : forall r n,
  r > 1 -> (n > 0)%nat -> r ^ n > 1.
Proof.
  intros r n H1 H2. induction n as [| k IH].
  - lia.
  - simpl. destruct k.
    -- simpl. lra.
    -- assert (r ^ S k > 1) by (apply IH; lia). nra.
Qed.

Lemma lemma_2_19 : forall n h,
  h > -1 -> (1 + h) ^ n >= 1 + INR n * h.
Proof.
  intros n h H1. induction n as [| k IH].
  - simpl. lra.
  - pose proof (Rtotal_order h 0) as [H2 | [H2 | H2]].
    -- rewrite S_INR. replace ((1+h)^S k) with ((1 + h)^k + h * (1 + h)^k) by (simpl; lra).
       replace (1 + (INR k + 1) * h) with (1 + INR k * h + h) by lra. assert ((1 + h)^k > 0) as H3 by (apply Rpow_gt_0; nra).
       destruct k. { compute. lra. } assert ((1 + h) ^ S k < 1) as H4 by (apply Rpow_lt_1; try nra; try lia). nra.
    -- simpl. nra.
    -- rewrite S_INR. replace ((1+h)^S k) with ((1 + h)^k + h * (1 + h)^k) by (simpl; lra).
       replace (1 + (INR k + 1) * h) with (1 + INR k * h + h) by lra. assert ((1 + h)^k > 0) as H3 by (apply Rpow_gt_0; nra).
       destruct k. { compute. lra. } assert ((1 + h) ^ S k > 1) as H4 by (apply Rpow_gt_1; try nra; try lia). nra.
Qed.

Fixpoint Fibonacci (n : nat) : R :=
  match n with
  | O => 0
  | S O => 1
  | S (S n'' as n') => Fibonacci n' + Fibonacci n''
  end.

Lemma lemma_2_20 : forall n,
  Fibonacci n = (((1 + sqrt 5)/2)^n - ((1 - sqrt 5)/2)^n) / sqrt 5.
Proof.
  apply strong_induction_N.
  intros n IH. destruct n as [| n'].
  - simpl. lra.
  - assert (H1 : 0 < sqrt 5) by (apply sqrt_lt_R0; lra). destruct n' as [| n''].
    -- simpl. field. lra.
    -- replace (Fibonacci (S (S n''))) with (Fibonacci (S n'') + Fibonacci n'') by auto.
       rewrite IH. 2 : { lia. } rewrite IH. 2 : { lia. } apply Rmult_eq_reg_r with (r := sqrt 5). 2 : { lra. }
       replace (((((1 + sqrt 5) / 2) ^ S n'' - ((1 - sqrt 5) / 2) ^ S n'') / sqrt 5 + (((1 + sqrt 5) / 2) ^ n'' - ((1 - sqrt 5) / 2) ^ n'') / sqrt 5) * sqrt 5)
       with (((((1 + sqrt 5) / 2) ^ S n'' - ((1 - sqrt 5) / 2) ^ S n'') + (((1 + sqrt 5) / 2) ^ n'' - ((1 - sqrt 5) / 2) ^ n''))) by (field; lra).
       replace ((((1 + sqrt 5) / 2) ^ S (S n'') - ((1 - sqrt 5) / 2) ^ S (S n'')) / sqrt 5 * sqrt 5)
       with ((((1 + sqrt 5) / 2) ^ S (S n'') - ((1 - sqrt 5) / 2) ^ S (S n''))) by (field; lra).
       replace (((1 + sqrt 5) / 2) ^ S n'' - ((1 - sqrt 5) / 2) ^ S n'' + (((1 + sqrt 5) / 2) ^ n'' - ((1 - sqrt 5) / 2) ^ n''))
       with (((1 + sqrt 5) / 2)^ S n'' + ((1 + sqrt 5) / 2) ^ n'' - ((1 - sqrt 5) / 2) ^ S n'' - ((1 - sqrt 5) / 2) ^ n'') by lra.
       replace (((1 + sqrt 5) / 2) ^ S n'' + ((1 + sqrt 5) / 2) ^ n'') with (((1 + sqrt 5) / 2) ^ n'' * (1 + ((1 + sqrt 5) / 2))) by (simpl; lra).
       replace (((1 + sqrt 5) / 2) ^ n'' * (1 + (1 + sqrt 5) / 2) - ((1 - sqrt 5) / 2) ^ S n'' - ((1 - sqrt 5) / 2) ^ n'') with
       (((1 + sqrt 5) / 2) ^ n'' * (1 + (1 + sqrt 5) / 2) - (1 - sqrt 5) / 2 * ((1 - sqrt 5) / 2) ^ n'' - ((1 - sqrt 5) / 2) ^ n'') by (simpl; lra).
       replace (((1 + sqrt 5) / 2) ^ n'' * (1 + (1 + sqrt 5) / 2) - (1 - sqrt 5) / 2 * ((1 - sqrt 5) / 2) ^ n'' - ((1 - sqrt 5) / 2) ^ n'') with
       (((1 + sqrt 5) / 2) ^ n'' * (1 + (1 + sqrt 5) / 2) - ((1 - sqrt 5) / 2) ^ n'' * (1 + ((1 - sqrt 5) / 2))) by (simpl; lra).
       replace (1 + ((1 - sqrt 5) / 2)) with (((1 - sqrt 5) / 2)^2).
       2 : { replace (((1 - sqrt 5) / 2)^2) with ((1 - 2 * sqrt 5 + sqrt 5 * sqrt 5) / 4). 2 : { simpl. field. } rewrite sqrt_sqrt. 2 : { lra. } field. }
       replace (1 + (1 + sqrt 5) / 2) with (((1 + sqrt 5) / 2)^2).
       2 : { replace (((1 + sqrt 5) / 2)^2) with ((1 + 2 * sqrt 5 + sqrt 5 * sqrt 5) / 4). 2 : { simpl. field. } rewrite sqrt_sqrt. 2 : { lra. } field. }
       replace (((1 + sqrt 5) / 2) ^ n'' * ((1 + sqrt 5) / 2) ^ 2) with (((1 + sqrt 5) / 2) ^ (S (S n''))). 2 : { simpl. field. }
       replace (((1 - sqrt 5) / 2) ^ n'' * ((1 - sqrt 5) / 2) ^ 2) with (((1 - sqrt 5) / 2) ^ (S (S n''))). 2 : { simpl. field. }
       field.
Qed.

Lemma nth_cons_f_mult : forall (l1 l2 : list R) (i : nat),
  (length l1 = length l2)%nat -> (nth i l1 0) * (nth i l2 0) = nth i (map (fun x => (fst x) * (snd x)) (combine l1 l2)) 0.
Proof.
  intros l1 l2 i H1. set (f := fun x : R * R => fst x * snd x). replace 0 with (f (0, 0)) at 3 by (compute; lra). rewrite map_nth. rewrite combine_nth; try lia. reflexivity.
Qed.

Lemma sum_f_nonneg : forall f i n,
  (i <= n)%nat ->
  (forall k, (i <= k <= n)%nat -> 0 <= f k) -> 0 <= sum_f i n f.
Proof.
  intros f i n H1 H2. unfold sum_f. induction n as [| n' IH].
  - simpl. apply H2. lia.
  - assert (H3 : (i = S n')%nat \/ (i < S n')%nat) by lia. destruct H3 as [H3 | H3].
    -- replace (S n' - i)%nat with 0%nat by lia. simpl. apply H2. lia.
    -- replace (S n' - i)%nat with (S (n' - i)%nat) by lia. repeat rewrite sum_f_R0_f_Sn.
       rewrite IH; try lia. replace (S (n' - i) + i)%nat with (S n')%nat by lia. assert (0 <= f (S n')) as H4.
       { apply H2. lia. } lra. intros k H5. apply H2. lia.
Qed.

Lemma sum_f_0_terms_nonneg : forall i n f,
  sum_f i n f = 0 -> (forall j, (i <= j <= n)%nat -> 0 <= f j) -> (forall j, (i <= j <= n)%nat -> f j = 0).
Proof.
  intros i n f H1 H2 j H3. induction n as [| k IH].
  - assert (i = 0%nat) as H4 by lia. assert (j = 0%nat) as H5 by lia. rewrite H4 in H1. rewrite sum_f_0_0 in H1. rewrite H5. apply H1.
  - assert (H4 : (i = S k)%nat \/ (i < S k)%nat) by lia. destruct H4 as [H4 | H4].
    -- rewrite <- H4 in H1. rewrite sum_f_n_n in H1. assert (j = i)%nat as H5 by lia. rewrite H5. apply H1.
    -- assert (i <= k)%nat as H5 by lia. assert (H2' : forall j : nat, (i <= j <= k)%nat -> 0 <= f j). intros j2 H6. apply H2; try lia.
       pose proof (sum_f_nonneg f i k H5 H2') as H6. rewrite sum_f_i_Sn_f in H1; try lia. assert (j = S k \/ (i <= j <= k)%nat) as [H7 | H7] by lia.
       ++ specialize (H2 j H3). rewrite <- H7 in H1. pose proof (Rtotal_order (sum_f i k f) 0) as [H8 | [H8 | H8]]; try nra.
       ++ apply IH; try lia. destruct H6 as [H6 | H6]; try nra. assert (i <= (S k) <= S k)%nat as H8 by lia. specialize (H2 (S k) H8). nra.
          intros j2 H9. apply H2. lia.
Qed.

Lemma sum_f_eq_0 : forall i n f,
  (i <= n)%nat -> (forall j, (i <= j <= n)%nat -> f j = 0) -> sum_f i n f = 0.
Proof.
  intros i n f H1 H2. induction n as [| k IH].
  - assert (i = 0%nat) as H3 by lia. rewrite H3. rewrite sum_f_0_0. apply H2. lia.
  - assert (H3 : (i = S k)%nat \/ (i < S k)%nat) by lia. destruct H3 as [H3 | H3].
    -- rewrite <- H3. rewrite sum_f_n_n. apply H2. lia.
    -- assert (i <= k)%nat as H4 by lia. assert (H2' : forall j : nat, (i <= j <= k)%nat -> f j = 0). intros j H5. apply H2; lia.
       rewrite sum_f_i_Sn_f; try lia. rewrite IH; try lia. rewrite H2; try lia. lra. intros j H5. apply H2. lia.
Qed.

Lemma lemma_2_21_a : forall (l1 l2 : list R),
  (length l1 = length l2)%nat -> (exists lam, map (fun x => x * lam) l2 = l1) ->
  sum_f 0 (length l1 - 1) (fun i => nth i l1 0 * nth i l2 0) <=
  sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2)).
Proof.
  intros l1 l2 H1 [lam H2]. assert (H3 : forall i, nth i l2 0 * lam = nth i l1 0).
  { intros i. rewrite <- H2. rewrite <- map_nth with (f := fun x => x * lam). rewrite Rmult_0_l. reflexivity. }
  assert (H4 : (sum_f 0 (length l1 - 1) (fun i => nth i l1 0 * nth i l2 0)) ^ 2 = (sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2)))^2).
  { rewrite Rpow_mult_distr. repeat rewrite pow2_sqrt; try (apply sum_f_nonneg; try lia; intros; apply pow2_ge_0).
    replace ((fun i : nat => nth i l1 0 * nth i l2 0)) with ((fun i : nat => lam * (nth i l2 0)^2)).
    2 : { apply functional_extensionality; intros i. rewrite <- H3. lra. } replace (fun i : nat => nth i l1 0 ^ 2) with (fun i : nat => lam * lam * (nth i l2 0) ^ 2).
    2 : { apply functional_extensionality; intros i. rewrite <- H3. lra. } repeat rewrite <- r_mult_sum_f_i_n_f_l. nra. } 
  assert (lam >= 0 \/ lam < 0) as [H5 | H5] by lra.
  - apply Req_le. apply Rsqr_inj. 2 : { rewrite <- sqrt_mult; try (apply sum_f_nonneg; try lia; intros; apply pow2_ge_0). apply sqrt_pos. }
    apply sum_f_nonneg; try lia; intros i H6. rewrite <- H3. nra. repeat rewrite Rsqr_def. nra.
  - repeat rewrite <- Rsqr_pow2 in H4. apply Rsqr_eq_abs_0 in H4. rewrite <- sqrt_mult in H4; try (apply sum_f_nonneg; try lia; intros; apply pow2_ge_0).
    pose proof (sqrt_pos (sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 ^ 2) * sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2))) as H6.
    solve_abs; try (rewrite <- sqrt_mult; try nra; try (apply sum_f_nonneg; try lia; intros; apply pow2_ge_0)).
Qed.

Lemma lemma_2_21_a' : forall (l1 l2 : list R),
  (length l1 = length l2)%nat ->
  Forall (fun x => x = 0) l2 -> 
  sum_f 0 (length l1 - 1) (fun i => nth i l1 0 * nth i l2 0) =
  sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2)).
Proof.
  intros l1 l2 H1 H2. assert (H3 : forall i, nth i l2 0 = 0).
  { intros i. assert (i >= length l1 \/ i < length l1)%nat as [H3 | H3] by lia. repeat rewrite nth_overflow; try lia; try lra. rewrite Forall_forall in H2. apply H2. apply nth_In. lia. } 
  replace ((fun i : nat => nth i l1 0 * nth i l2 0)) with (fun i : nat => 0). 2 : { apply functional_extensionality; intros i. rewrite H3. lra. }
  replace ((fun i : nat => nth i l2 0 ^ 2)) with (fun i : nat => 0). 2 : { apply functional_extensionality; intros i. rewrite H3. lra. } rewrite sum_f_const.
  rewrite Rmult_0_l. rewrite sqrt_0. lra.
Qed.

Lemma cons_neq : forall (r1 r2 : R) (t1 t2 : list R),
  r1 :: t1 <> r2 :: t2 -> r1 <> r2 \/ t1 <> t2.
Proof.
 intros r1 r2 t1 t2 H1. destruct (Req_dec r1 r2) as [H2 | H2].
 - right. intros H3. apply H1. rewrite H2. rewrite H3. reflexivity.
 - left. auto.
Qed.

Lemma list_neq_exists_nth_neq : forall (l1 l2 : list R),
  (length l1 = length l2)%nat -> l1 <> l2 -> exists i, (0 <= i <= length l1 - 1)%nat /\ nth i l1 0 <> nth i l2 0.
Proof.
  intros l1 l2 H1 H2. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2 H1 H2. simpl in H1. apply eq_sym in H1. apply length_zero_iff_nil in H1. apply eq_sym in H1. tauto.
  - intros l2 H1 H2. destruct l2 as [| h2 t2].
    -- simpl in H1. lia.
    -- simpl in H1. assert (H3 : (length t1 = length t2)%nat) by lia. apply cons_neq in H2 as [H2 | H2].
       + exists 0%nat. split; simpl; try lia; auto.
       + specialize (IH t2 H3 H2) as [k [H4 H5]]. exists (S k). assert (H6 : t1 <> []).
         { destruct t1. apply eq_sym in H3. apply length_zero_iff_nil in H3. rewrite <- H3. auto. discriminate. }
         assert (H7 : (length t1 > 0)%nat). { destruct t1. tauto. simpl. lia. } split; simpl in *; try lia; auto.
Qed.

Lemma map_r_neq : forall (l1 l2 : list R) r,
  (length l1 = length l2)%nat -> map (fun x => x * r) l2 <> l1 -> exists i, (0 <= i <= length l2 - 1)%nat /\ r * nth i l2 0 <> nth i l1 0.
Proof.
  intros l1 l2 r H1 H2. assert (H3 : (length l1 = length (map (fun x => x * r)%R l2))%nat) by (rewrite map_length; auto). apply list_neq_exists_nth_neq in H3 as [i [H4 H5]]; auto.
  exists i. split; try lia. intros H6. apply H5. rewrite <- H6. set (f := fun x => x * r). replace 0 with (f 0) at 2 by (unfold f; lra). rewrite map_nth. unfold f. lra.
Qed.

Lemma pow2_gt_0 : forall r,
  r <> 0 -> r ^ 2 > 0.
Proof.
  intros r H1. destruct (Rlt_dec r 0) as [H2 | H2].
  - simpl. rewrite Rmult_1_r. apply Rmult_neg_neg; auto.
  - assert (H3 : r > 0) by lra. apply Rmult_gt_0_compat; lra.
Qed.

Lemma map_Rmult_0 : forall (l : list R),
  map (fun x => x * 0) l = repeat 0%R (length l).
Proof.
  intros l. induction l as [| h t IH].
  - reflexivity.
  - simpl. rewrite IH. rewrite Rmult_0_r. reflexivity.
Qed.

Lemma lemma_2_21_a'' : forall (l1 l2 : list R),
  (length l1 = length l2)%nat -> 
  (~Forall (fun x => x = 0) l2) ->
  (forall lam, map (fun x => x * lam) l2 <> l1) ->
  sum_f 0 (length l1 - 1) (fun i => nth i l1 0 * nth i l2 0) <= 
  sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2)).
Proof.
  intros l1 l2 H1 H2 H3.
  assert (H4 : 0 < sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2)).
  { 
    apply sum_f_pos'; try lia. intros i H5. apply pow2_ge_0. apply neg_Forall_Exists_neg in H2. 2 : { intros x. apply Req_dec_T. } apply Exists_exists in H2 as [k [H2 H4]]. apply In_nth with (d := 0) in H2 as [i [H5 H6]].
    exists i. split; try lia. apply pow2_gt_0. lra.
  }
  assert (H5 : forall lam, lam ^ 2 + -2 * (sum_f 0 (length l1 - 1) (fun i => nth i l1 0 * nth i l2 0)) / sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2) * lam + sum_f 0 (length l1 - 1) (fun i => nth i l1 0 ^ 2) / sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2) <> 0).
  {
    intros lam. specialize (H3 lam). 
    assert (H5 : 0 < sum_f 0 (length l1 - 1) (fun i => (lam * nth i l2 0 - nth i l1 0)^2)).
    {
      apply sum_f_pos'; try lia. intros i H5. apply pow2_ge_0. assert (length l2 > 0)%nat as H5. { destruct l1, l2; simpl in *; try lia; try tauto. } apply map_r_neq in H3 as [k [H6 H7]]; try lia.
      exists k. split; try lia. apply pow2_gt_0. lra.
    }
    replace ((fun i : nat => (lam * nth i l2 0 - nth i l1 0) ^ 2)) with (fun i : nat => lam ^ 2 * (nth i l2 0) ^ 2 + (-2 * lam) * nth i (map (fun x : R * R => fst x * snd x) (combine l1 l2)) 0 + nth i l1 0 ^ 2) in H5.
    2 : { apply functional_extensionality; intros i. rewrite <- nth_cons_f_mult; try lia. nra. } do 2 (rewrite <- sum_f_plus in H5; try lia). do 2 rewrite <- r_mult_sum_f_i_n_f_l in H5.
    replace ((fun i : nat => nth i (map (fun x : R * R => fst x * snd x) (combine l1 l2)) 0)) with ((fun i : nat => nth i l1 0 * nth i l2 0)) in H5.
    2 : { apply functional_extensionality; intros i. rewrite <- nth_cons_f_mult; try lia. reflexivity. }
    apply Rmult_lt_compat_r with (r := / sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2)) in H5. 2 : { apply Rinv_pos; lra. } rewrite Rmult_0_l in H5. repeat rewrite Rmult_plus_distr_r in H5.
    replace (lam ^ 2 * sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2) * / sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2)) with (lam ^ 2) in H5 by (field; lra). nra.
  }
  apply lemma_1_18_a'' in H5.
  replace ((-2 * sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 * nth i l2 0) / sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2)) ^ 2) with 
          (4 * ((sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 * nth i l2 0) ^ 2) / (sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2) ^ 2))) in H5 by (field; nra).
  apply Rmult_lt_compat_l with (r := 1/4) in H5; try nra. rewrite Rmult_minus_distr_l in H5. field_simplify in H5; try lra. replace (0 / 4) with 0 in H5 by nra.
  apply Rmult_lt_compat_r with (r := sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2)) in H5; try lra. rewrite Rmult_0_l in H5. unfold Rdiv in H5. rewrite Rmult_assoc in H5. field_simplify in H5; try lra.
  assert (H6 : ~Forall (fun x => x = 0) l1).
  {
    intros H6. apply (H3 0). rewrite map_Rmult_0. apply eq_sym. rewrite <- H1. apply Forall_eq_repeat. apply Forall_forall. intros x H7. rewrite Forall_forall in H6. specialize (H6 x H7). lra.
  }
  assert (H7 : 0 < sum_f 0 (length l1 - 1) (fun i => nth i l1 0 ^ 2)).
  {
    apply sum_f_pos'; try lia. intros i H7. apply pow2_ge_0. apply neg_Forall_Exists_neg in H6. 2 : { intros x. apply Req_dec_T. } apply Exists_exists in H6 as [k [H6 H8]]. apply In_nth with (d := 0) in H6 as [i [H7 H9]].
    exists i. split; try lia. apply pow2_gt_0. lra.
  }
  assert (H8 : sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2) * sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 ^ 2) / sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2) > 0) by (apply Rdiv_pos_pos; try nra).
  apply Rplus_lt_compat_r with (r := sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2) * sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 ^ 2) / sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2)) in H5.
  field_simplify in H5; try nra.
  apply Rmult_lt_compat_r with (r := sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2)) in H5; try nra. field_simplify in H5; try nra. apply sqrt_lt_1 in H5; try nra.
  pose proof (sqrt_pos (sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2) * sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 ^ 2))) as H9. rewrite <- sqrt_mult; try nra. rewrite Rmult_comm.
  pose proof (Rtotal_order (sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 * nth i l2 0)) 0) as [H10 | [H10 | H10]]; try nra.
  rewrite sqrt_pow2 in H5; try nra.
Qed.

Lemma lemma_2_21_a''' : forall (l1 l2 : list R),
  (length l1 = length l2)%nat -> 
  sum_f 0 (length l1 - 1) (fun i => nth i l1 0 * nth i l2 0) <= 
  sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2)).
Proof.
  intros l1 l2 H1. pose proof (classic ((~Forall (fun x => x = 0) l2) /\ forall lam, map (fun x => x * lam) l2 <> l1)) as [[H2 H3]| H3].
  - apply lemma_2_21_a''; auto.
  - apply not_and_or in H3 as [H3 | H3].
    -- apply NNPP in H3. apply Req_le. apply lemma_2_21_a'; auto.
    -- apply not_all_ex_not in H3 as [lam H3]. assert (H4 : map (fun x => x * lam) l2 = l1) by tauto. apply lemma_2_21_a; auto. exists lam. auto.
Qed.

Lemma lemma_2_21_b : forall (l1 l2 : list R),
  (length l1 = length l2)%nat -> 
  sum_f 0 (length l1 - 1) (fun i => nth i l1 0 * nth i l2 0) <= 
  sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2)).
Proof.
  intros l1 l2 H1. assert (H2 : forall x y, 0 <= x^2 - 2*x*y + y^2).
  { intros x y. replace (x^2 - 2*x*y + y^2) with ((x - y)^2) by field. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
  assert (forall x y, 2*x*y <= x^2 + y^2) as H3. { intros x y. specialize (H2 x y). lra. }
  assert (H4 : forall i : nat, (2 * nth i l1 0 * nth i l2 0) / (sqrt (sum_f 0 (length l1 - 1) (fun j => nth j l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun j => nth j l2 0 ^ 2))) <= (nth i l1 0 ^ 2) / (sum_f 0 (length l1 - 1) (fun j => nth j l1 0 ^ 2)) + (nth i l2 0 ^ 2) / (sum_f 0 (length l1 - 1) (fun j => nth j l2 0 ^ 2))).
  {
    intros i. assert (i >= length l1 \/ i < length l1)%nat as [H4 | H4] by lia. repeat rewrite nth_overflow; try lia. nra. 
    specialize (H3 (nth i l1 0 / (sqrt (sum_f 0 (length l1 - 1) (fun j => nth j l1 0 ^2)))) (nth i l2 0 / (sqrt (sum_f 0 (length l1 - 1) (fun j => nth j l2 0 ^ 2))))).
    repeat rewrite <- Rsqr_pow2 in H3. repeat rewrite Rsqr_div' in H3. repeat rewrite Rsqr_pow2 in H3. rewrite pow2_sqrt in H3. rewrite pow2_sqrt in H3.
    2 : { apply sum_f_nonneg. lia. intros k H5. apply pow2_ge_0. } 2 : { apply sum_f_nonneg. lia. intros k H5. apply pow2_ge_0. }
    assert (0 <= sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2)) as H5. { apply sum_f_nonneg. lia. intros j H5. apply pow2_ge_0. }
    assert (0 <= sum_f 0 (length l1 - 1) (fun j : nat => nth j l1 0 ^ 2)) as H6. { apply sum_f_nonneg. lia. intros j H6. apply pow2_ge_0. }
    destruct H5 as [H5 | H5]; destruct H6 as [H6 | H6].
    - replace (2 * (nth i l1 0 / sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l1 0 ^ 2))) * (nth i l2 0 / sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2)))) with 
            (2 * nth i l1 0 * nth i l2 0 / (sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2)))) in H3.
      2 : { field. split; intro H7; apply sqrt_lt_R0 in H5, H6; lra. } nra.
    - rewrite <- H6 in *. rewrite sqrt_0 in *. rewrite Rmult_0_l. unfold Rdiv. rewrite Rinv_0. field_simplify. assert (0 <= nth i l2 0 ^ 2) as H7. { apply pow2_ge_0. }
      2 : { nra. } destruct H7 as [H7 | H7]; try lra. apply Rlt_le. apply Rdiv_lt_0_compat; try lra. rewrite <- H7. lra.
    - rewrite <- H5 in *. rewrite sqrt_0 in *. rewrite Rmult_0_r. unfold Rdiv. rewrite Rinv_0. field_simplify. assert (0 <= nth i l1 0 ^ 2) as H7. { apply pow2_ge_0. }
      2 : { nra. } destruct H7 as [H7 | H7]; try lra. apply Rlt_le. apply Rdiv_lt_0_compat; try lra. rewrite <- H7. lra.
    - rewrite <- H5 in *. rewrite <- H6 in *. rewrite sqrt_0 in *. rewrite Rmult_0_l. unfold Rdiv. rewrite Rinv_0. nra.
  }
  set (f1 := fun i : nat => 2 * nth i l1 0 * nth i l2 0 / (sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2)))).
  set (f2 := fun i : nat => nth i l1 0 ^ 2 / sum_f 0 (length l1 - 1) (fun j : nat => nth j l1 0 ^ 2) + nth i l2 0 ^ 2 / sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2)).
  assert (H5 : forall i, (0 <= i <= length l1 - 1)%nat -> f1 i <= f2 i). { intros i H5. apply H4. }
  apply sum_f_congruence_le in H5; try lia. unfold f1, f2 in H5. rewrite <- sum_f_plus in H5; try lia.
  pose proof (Rtotal_order (sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 ^2)) 0) as H6. pose proof (Rtotal_order (sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^2)) 0) as H7.
  destruct H6 as [H6 | [H6 | H6]]; destruct H7 as [H7 | [H7 | H7]].
  - assert (0 <= sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 ^ 2)) as H8. { apply sum_f_nonneg. lia. intros j H8. apply pow2_ge_0. } lra.
  - assert (0 <= sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 ^ 2)) as H8. { apply sum_f_nonneg. lia. intros j H8. apply pow2_ge_0. } lra.
  - assert (0 <= sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 ^ 2)) as H8. { apply sum_f_nonneg. lia. intros j H8. apply pow2_ge_0. } lra.
  - assert (sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 * nth i l2 0) = 0) as H8. 
    { apply sum_f_eq_0; try lia. intros j H8. apply sum_f_0_terms_nonneg with (j := j%nat) in H6; try lia. 2 : { intros k H9. apply pow2_ge_0. } nra. }
    rewrite H8. rewrite H6. rewrite sqrt_0. lra.
  - assert (sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 * nth i l2 0) = 0) as H8. 
    { apply sum_f_eq_0; try lia. intros j H8. apply sum_f_0_terms_nonneg with (j := j%nat) in H7; try lia. 2 : { intros k H9. apply pow2_ge_0. } nra. }
    rewrite H8. rewrite H7. rewrite sqrt_0. lra.
  - assert (sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 * nth i l2 0) = 0) as H8. 
    { apply sum_f_eq_0; try lia. intros j H8. apply sum_f_0_terms_nonneg with (j := j%nat) in H6; try lia. 2 : { intros k H9. apply pow2_ge_0. } nra. }
    rewrite H8. rewrite H6. rewrite sqrt_0. lra.
  - assert (0 <= sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2)) as H8. { apply sum_f_nonneg. lia. intros j H8. apply pow2_ge_0. } lra.
  - assert (sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 * nth i l2 0) = 0) as H8.
    { apply sum_f_eq_0; try lia. intros j H8. apply sum_f_0_terms_nonneg with (j := j%nat) in H7; try lia. 2 : { intros k H9. apply pow2_ge_0. } nra. }
    rewrite H8. rewrite H7. rewrite sqrt_0. lra.
  - replace (sum_f 0 (length l1 - 1) (fun i : nat => nth i l1 0 ^ 2 / sum_f 0 (length l1 - 1) (fun j : nat => nth j l1 0 ^ 2))) with 1 in H5.
    2 : { unfold Rdiv. rewrite <- r_mult_sum_f_i_n_f. field. lra. } 
    replace (sum_f 0 (length l1 - 1) (fun i : nat => nth i l2 0 ^ 2 / sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2))) with 1 in H5.
    2 : { unfold Rdiv. rewrite <- r_mult_sum_f_i_n_f. field. lra. } 
    replace (fun i : nat => 2 * nth i l1 0 * nth i l2 0 / (sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2)))) with 
            ((fun i : nat => (2 * / (sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2)))) * (nth i l1 0 * nth i l2 0))) in H5.
    2 : { apply functional_extensionality. intros i. nra. } rewrite <- r_mult_sum_f_i_n_f_l in H5. apply Rmult_le_compat_l with (r := 1/2 * (sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l1 0 ^ 2)))) in H5. 
    2 : { apply Rmult_le_reg_l with (r := 2); try nra. field_simplify. apply sqrt_pos. } field_simplify in H5.
          2 : { apply Rgt_lt in H6, H7. pose proof sqrt_lt_R0 as H8. split. specialize (H8 (sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2)) H7). lra.
                specialize (H8 (sum_f 0 (length l1 - 1) (fun j : nat => nth j l1 0 ^2)) H6). lra. } 
    apply Rmult_le_compat_r with (r := sqrt (sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2))) in H5. 2 : { apply sqrt_pos. } field_simplify in H5.
    2 : { apply Rgt_lt in H7. pose proof sqrt_lt_R0 as H8. specialize (H8 (sum_f 0 (length l1 - 1) (fun j : nat => nth j l2 0 ^ 2)) H7). lra. } lra.
Qed.

Lemma lemma_2_21_c_helper1 : forall (l1 l2 : list R),
  (length l1 = length l2)%nat -> sum_f 0 (length l1 - 1) (fun i => (nth i l1 0)^2) * sum_f 0 (length l1 - 1) (fun i => (nth i l2 0)^2) = 
  (sum_f 0 (length l1 - 1) (fun i => (nth i l1 0 * nth i l2 0)^2) + sum_f 0 (length l1 - 1) (fun i => sum_f 0 (length l1 - 1) (fun j => if (i =? j)%nat then 0 else ((nth i l1 0 * nth j l2 0)^2)))).
Proof.
  intros l1 l2 H1. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2 H1. simpl. repeat rewrite sum_f_0_0. simpl. rewrite nth_overflow; try lia. lra. rewrite <- H1. simpl. lia.
  - intros l2 H1. destruct l2 as [| h2 t2]; try inversion H1 as [H2]. specialize (IH t2 H2). replace (length (h1 :: t1) - 1)%nat with (length t1). 2 : { simpl. lia. }
    destruct (length t1) as [| n].
    -- repeat rewrite sum_f_0_0. simpl. lra.
    -- inversion H1 as [H3]. simpl in H1. replace (S n - 1)%nat with n%nat in IH by lia. rewrite sum_f_Si with (f := fun i : nat => sum_f 0 (S n) (fun j : nat => if (i =? j)%nat then 0 else (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0) ^ 2)); try lia.
       rewrite sum_f_Si with (f := fun j : nat => if (0 =? j)%nat then 0 else (nth 0 (h1 :: t1) 0 * nth j (h2 :: t2) 0) ^ 2); try lia. assert (0 =? 0 = true)%nat as H4 by (compute; reflexivity). rewrite H4. field_simplify.
       replace (sum_f 1 (S n) (fun j : nat => if (0 =? j)%nat then 0 else (nth 0 (h1 :: t1) 0 * nth j (h2 :: t2) 0) ^ 2)) with (h1^2 * sum_f 1 (S n) (fun j : nat => nth j (h2 :: t2) 0 ^ 2)).
       2 : { rewrite r_mult_sum_f_i_n_f. apply sum_f_equiv; try lia. intros j H5. assert (0 =? j = false)%nat as H6. { compute. destruct j; lia. } rewrite H6. simpl. lra. }
       rewrite H2. rewrite sum_f_nth_cons_2; try lia. replace (length t2 - 1)%nat with n by lia. replace (sum_f 1 (length t2) (fun i : nat => sum_f 0 (length t2) (fun j : nat => if (i =? j)%nat then 0 else (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0) ^ 2)))
       with (sum_f 1 (length t2) (fun i : nat => ((nth i (h1 :: t1) 0 * h2)^2) + sum_f 1 (length t2) (fun j : nat => if (i =? j)%nat then 0 else (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0) ^ 2))).
       2 : { apply sum_f_equiv; try lia. intros i H5. rewrite <- H2. rewrite sum_f_Si with (i := 0%nat); try lia. assert (i =? 0 = false)%nat as H6. { compute. destruct i; lia. } rewrite H6. 
             replace ((nth i (h1 :: t1) 0 * nth 0 (h2 :: t2) 0) ^ 2) with ((nth i (h1 :: t1) 0 * h2) ^ 2) by (simpl; lra). lra. }
       rewrite <- sum_f_plus; try lia. 
       replace ((sum_f 1 (length t2) (fun i : nat => (nth i (h1 :: t1) 0 * h2) ^ 2))) with (h2^2 * sum_f 0 n (fun i : nat => (nth i t1 0) ^ 2)).
       2 : { rewrite r_mult_sum_f_i_n_f. rewrite sum_f_reindex' with (s := 1%nat). rewrite <- H2. replace (n + 1)%nat with (S n) by lia. apply sum_f_equiv; try lia. intros i H5. 
             replace (h1 :: t1) with ([h1] ++ t1) by reflexivity. rewrite app_nth2; try (simpl; lia). simpl. lra. }
       replace (sum_f 1 (length t2) (fun i : nat => sum_f 1 (length t2) (fun j : nat => if (i =? j)%nat then 0 else (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0) ^ 2))) with 
               (sum_f 0 (n) (fun i : nat => sum_f 0 (n) (fun j : nat => if (i =? j)%nat then 0 else (nth i t1 0 * nth j t2 0) ^ 2))).
       2 : { rewrite <- H2. rewrite sum_f_reindex' with (s := 1%nat). replace (n + 1)%nat with (S n) by lia. apply sum_f_equiv; try lia. intros i H5. 
             rewrite sum_f_reindex' with (s := 1%nat). replace (n + 1)%nat with (S n) by lia. apply sum_f_equiv; try lia. intros j H6.
             assert (i - 1 = j - 1 \/ i - 1 <> j - 1)%nat as [H7 | H7] by lia.
             - assert (i = j) as H8 by lia. apply Nat.eqb_eq in H7, H8. rewrite H7, H8. reflexivity.
             - assert (i <> j) as H8 by lia. apply Nat.eqb_neq in H7, H8. rewrite H7, H8. replace (h1 :: t1) with ([h1] ++ t1) by reflexivity.
               replace (h2 :: t2) with ([h2] ++ t2) by reflexivity. repeat (rewrite app_nth2; try (simpl; lia)). simpl. lra. }
       apply Rminus_eq_compat_r with (r := sum_f 0 n (fun i : nat => (nth i t1 0 * nth i t2 0) ^ 2)) in IH. field_simplify in IH. rewrite <- IH. 
       rewrite <- H3 at 1. repeat rewrite sum_f_nth_cons_1; try lia. replace (fun i : nat => (nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0) ^ 2) with (fun i : nat => nth i ((h1 * h2) :: map (fun x => (fst x) * (snd x)) (combine (t1) (t2))) 0 ^ 2).
       2 : { apply functional_extensionality. intros i. rewrite nth_cons_f_mult; try (simpl; lia). replace (combine (h1 :: t1) (h2 :: t2)) with ((h1, h2) :: combine t1 t2) by reflexivity. rewrite map_cons. destruct i; simpl; try lra. } 
       replace (length t2) with (length (map (fun x : R * R => fst x * snd x) (combine t1 t2))) at 2 by (rewrite map_length; rewrite combine_length; lia). rewrite sum_f_nth_cons_1. 2 : { rewrite map_length. rewrite combine_length. lia. }
       replace (Nat.sub (length (map (fun x : R * R => fst x * snd x) (combine t1 t2))) 1%nat) with n by (rewrite map_length; rewrite combine_length; lia). 
       replace (fun i : nat => nth i (map (fun x : R * R => fst x * snd x) (combine t1 t2)) 0 ^ 2) with (fun i : nat => (nth i t1 0 * nth i t2 0) ^ 2).
       2 : { apply functional_extensionality. intros i. rewrite nth_cons_f_mult; try lia. reflexivity. } replace (length t2 - 1)%nat with n by lia. replace (length t1 -1)%nat with n by lia.
       field_simplify. reflexivity.
Qed.

Lemma lemma_2_21_c_helper2 : forall (l1 l2 : list R),
  (length l1 = length l2)%nat -> (sum_f 0 (length l1 - 1) (fun i => nth i l1 0 * nth i l2 0))^2 = (sum_f 0 (length l1 - 1) (fun i => (nth i l1 0 * nth i l2 0)^2) + 
  sum_f 0 (length l1 - 1) (fun i => sum_f 0 (length l1 - 1) (fun j => if (i =? j)%nat then 0 else (nth i l1 0 * nth i l2 0 * nth j l1 0 * nth j l2 0)))).
Proof.
  intros l1 l2 H1. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2 H1. simpl. repeat rewrite sum_f_0_0. simpl. rewrite nth_overflow; try lia. lra. rewrite <- H1. simpl. lia.
  - intros l2 H1. destruct l2 as [| h2 t2]; try inversion H1 as [H2]. specialize (IH t2 H2). replace (length (h1 :: t1) - 1)%nat with (length t1). 2 : { simpl. lia. }
    destruct (length t1) as [| n].
    -- repeat rewrite sum_f_0_0. simpl. lra.
    -- inversion H1 as [H3]. simpl in H1. replace (S n - 1)%nat with n%nat in IH by lia. rewrite sum_f_Si with (f := fun i : nat => sum_f 0 (S n) (fun j : nat => if (i =? j)%nat then 0 else nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0)); try lia.
       rewrite sum_f_Si with (f := fun j : nat => if (0 =? j)%nat then 0 else nth 0 (h1 :: t1) 0 * nth 0 (h2 :: t2) 0 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0); try lia. assert (0 =? 0 = true)%nat as H4 by (compute; reflexivity). rewrite H4. field_simplify.
       replace (sum_f 1 (S n) (fun j : nat => if (0 =? j)%nat then 0 else nth 0 (h1 :: t1) 0 * nth 0 (h2 :: t2) 0 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0)) with (h1 * h2 * sum_f 1 (S n) (fun j : nat => nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0)).
       2 : { rewrite r_mult_sum_f_i_n_f. apply sum_f_equiv; try lia. intros j H5. assert (0 =? j = false)%nat as H6. { compute. destruct j; lia. } rewrite H6. simpl. lra. } 
       replace (fun j : nat => nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0) with (fun j : nat => nth j ((h1 * h2) :: map (fun x => (fst x) * (snd x)) (combine t1 t2)) 0 * 1).
       2 : { apply functional_extensionality. intros j. rewrite nth_cons_f_mult; try (simpl; lia). simpl. destruct j; lra. }
       replace (S n) with (length (map (fun x : R * R => fst x * snd x) (combine t1 t2))) at 4. 2 : { rewrite map_length. rewrite combine_length. lia. } rewrite sum_f_nth_cons_2.  2 : { rewrite map_length. rewrite combine_length. lia. }
       replace (Nat.sub (length (map (fun x : R * R => fst x * snd x) (combine t1 t2))) 1) with n. 2 : { rewrite map_length. rewrite combine_length. lia. } replace ((fun i : nat => nth i (map (fun x : R * R => fst x * snd x) (combine t1 t2)) 0 * 1))
       with (fun i : nat => nth i t1 0 * nth i t2 0). 2 : { apply functional_extensionality. intros i. rewrite nth_cons_f_mult; try lia. lra. } rewrite H2. 
       replace (sum_f 1 (length t2) (fun i : nat => sum_f 0 (length t2) (fun j : nat => if (i =? j)%nat then 0 else nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0))) with 
               (sum_f 1 (length t2) (fun i : nat => nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * h1 * h2 + sum_f 1 (length t2) (fun j : nat => if (i =? j)%nat then 0 else nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0))).
       2 : { apply sum_f_equiv; try lia. intros i H5. rewrite <- H2. rewrite sum_f_Si with (i := 0%nat); try lia. assert (i =? 0 = false)%nat as H6. { compute. destruct i; lia. } rewrite H6. 
             replace (nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * nth 0 (h1 :: t1) 0 * nth 0 (h2 :: t2) 0) with (nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * h1 * h2) by (simpl; lra).  lra. }
       rewrite <- sum_f_plus; try lia. replace (sum_f 1 (length t2) (fun i : nat => nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * h1 * h2)) with (h1 * h2 * sum_f 0 n (fun i : nat => nth i t1 0 * nth i t2 0)).
       2 : { rewrite r_mult_sum_f_i_n_f. rewrite sum_f_reindex' with (s := 1%nat). rewrite <- H2. replace (n + 1)%nat with (S n) by lia. apply sum_f_equiv; try lia. intros i H5. 
             destruct i; simpl; try lra; try lia. rewrite Nat.sub_0_r. lra. }
       replace (sum_f 1 (length t2) (fun i : nat => sum_f 1 (length t2) (fun j : nat => if (i =? j)%nat then 0 else nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0))) with 
               (sum_f 0 (n) (fun i : nat => sum_f 0 (n) (fun j : nat => if (i =? j)%nat then 0 else nth i t1 0 * nth i t2 0 * nth j t1 0 * nth j t2 0))).
       2 : { rewrite <- H2. rewrite sum_f_reindex' with (s := 1%nat). replace (n + 1)%nat with (S n) by lia. apply sum_f_equiv; try lia. intros i H5. 
             rewrite sum_f_reindex' with (s := 1%nat). replace (n + 1)%nat with (S n) by lia. apply sum_f_equiv; try lia. intros j H6.
             assert (i - 1 = j - 1 \/ i - 1 <> j - 1)%nat as [H7 | H7] by lia.
             - assert (i = j) as H8 by lia. apply Nat.eqb_eq in H7, H8. rewrite H7, H8. reflexivity.
             - assert (i <> j) as H8 by lia. apply Nat.eqb_neq in H7, H8. rewrite H7, H8. replace (h1 :: t1) with ([h1] ++ t1) by reflexivity.
               replace (h2 :: t2) with ([h2] ++ t2) by reflexivity. repeat (rewrite app_nth2; try (simpl; lia)). simpl. lra. }
       apply Rminus_eq_compat_r with (r := sum_f 0 n (fun i : nat => (nth i t1 0 * nth i t2 0) ^ 2)) in IH. field_simplify in IH. rewrite <- IH.
       replace (length t2) with (length (map (fun x : R * R => fst x * snd x) (combine t1 t2))) at 1 by (rewrite map_length; rewrite combine_length; lia). rewrite sum_f_nth_cons_1. 2 : { rewrite map_length. rewrite combine_length. lia. }
       replace (Nat.sub (length (map (fun x : R * R => fst x * snd x) (combine t1 t2))) 1) with n by (rewrite map_length; rewrite combine_length; lia). 
       replace (fun i : nat => nth i (map (fun x : R * R => fst x * snd x) (combine t1 t2)) 0 * 1) with (fun i : nat => nth i t1 0 * nth i t2 0). 2 : { apply functional_extensionality. intros i. rewrite nth_cons_f_mult; try lia. lra. }
       replace ((fun i : nat => (nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0) ^ 2)) with (fun i : nat => nth i ((h1 * h2) :: map (fun x => (fst x) * (snd x)) (combine t1 t2)) 0 ^ 2).
       2 : { apply functional_extensionality. intros i. rewrite nth_cons_f_mult; try (simpl; lia). replace (combine (h1 :: t1) (h2 :: t2)) with ((h1, h2) :: combine t1 t2) by reflexivity. rewrite map_cons. destruct i; simpl; try lra. }
       replace (length t2)%nat with (length (map (fun x : R * R => fst x * snd x) (combine t1 t2))) at 1 by (rewrite map_length; rewrite combine_length; lia). rewrite sum_f_nth_cons_1. 2 : { rewrite map_length. rewrite combine_length. lia. }
       replace (Nat.sub (length (map (fun x : R * R => fst x * snd x) (combine t1 t2))) 1) with n by (rewrite map_length; rewrite combine_length; lia).
       replace (fun i : nat => nth i (map (fun x : R * R => fst x * snd x) (combine t1 t2)) 0 ^ 2) with (fun i : nat => (nth i t1 0 * nth i t2 0) ^ 2). 2 : { apply functional_extensionality. intros i. rewrite nth_cons_f_mult; try lia. reflexivity. }
       field_simplify. reflexivity.
Qed.

Lemma lemma_2_21_c_helper3 : forall (l1 l2 : list R),
  (length l1 = length l2)%nat -> sum_f 0 (length l1 - 1) (fun i => sum_f 0 (length l1 - 1) (fun j => if (i =? j)%nat then 0 else (nth i l1 0 * nth j l2 0)^2 - nth i l1 0 * nth i l2 0 * nth j l1 0 * nth j l2 0)) = 
                                 sum_f 0 (length l1 - 1) (fun i => sum_f 0 (length l1 - 1) (fun j => if (i <? j)%nat then (nth i l1 0 * nth j l2 0 - nth j l1 0 * nth i l2 0)^2 else 0)).
Proof.
  intros l1 l2 H1. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2 H1. compute. reflexivity.
  - intros l2 H1. destruct l2 as [| h2 t2]; try inversion H1 as [H2]. specialize (IH t2 H2). replace (length (h1 :: t1) - 1)%nat with (length t1). 2 : { simpl. lia. }
    destruct (length t1) as [| n].
    -- repeat rewrite sum_f_0_0. simpl. lra.
    -- inversion H1 as [H3]. simpl in H1. replace (S n - 1)%nat with n%nat in IH by lia. rewrite sum_f_Si with (f := (fun i : nat => sum_f 0 (S n) (fun j : nat => if (i <? j)%nat then (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0 - nth j (h1 :: t1) 0 * nth i (h2 :: t2) 0) ^ 2 else 0))); try lia.
       rewrite sum_f_Si with (f := fun j : nat => if (0 <? j)%nat then (nth 0 (h1 :: t1) 0 * nth j (h2 :: t2) 0 - nth j (h1 :: t1) 0 * nth 0 (h2 :: t2) 0) ^ 2 else 0); try lia.
       assert (0 <? 0 = false)%nat as H4 by (compute; reflexivity). rewrite H4. field_simplify.
       replace (sum_f 1 (S n) (fun j : nat => if (0 <? j)%nat then (nth 0 (h1 :: t1) 0 * nth j (h2 :: t2) 0 - nth j (h1 :: t1) 0 * nth 0 (h2 :: t2) 0) ^ 2 else 0)) with (sum_f 1 (S n) (fun j : nat => (h1 * nth j (h2 :: t2) 0 - h2 * nth j (h1 :: t1) 0) ^ 2)).
       2 : { apply sum_f_equiv; try lia. intros j H5. assert (0 <? j = true)%nat as H6. { apply Nat.ltb_lt. lia. } rewrite H6. simpl. lra. }
       replace (S n) with (length t1) at 3 by lia. rewrite sum_f_nth_cons_3; try lia. 
       replace (sum_f 1 (S n) (fun i : nat => sum_f 0 (S n) (fun j : nat => if (i <? j)%nat then (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0 - nth j (h1 :: t1) 0 * nth i (h2 :: t2) 0) ^ 2 else 0))) with 
               (sum_f 1 (S n) (fun i : nat => sum_f 1 (S n) (fun j : nat => if (i <? j)%nat then (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0 - nth j (h1 :: t1) 0 * nth i (h2 :: t2) 0) ^ 2 else 0))).
       2 : { apply sum_f_equiv; try lia. intros i H5. rewrite sum_f_Si with (i := 0%nat); try lia. assert (i <? 0 = false)%nat as H6. { apply Nat.ltb_ge. lia. } rewrite H6. lra. }
       replace (sum_f 1 (S n) (fun i : nat => sum_f 1 (S n) (fun j : nat => if (i <? j)%nat then (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0 - nth j (h1 :: t1) 0 * nth i (h2 :: t2) 0) ^ 2 else 0))) with 
               (sum_f 0 n (fun i : nat => sum_f 0 n (fun j : nat => if (i <? j)%nat then (nth i t1 0 * nth j t2 0 - nth j t1 0 * nth i t2 0) ^ 2 else 0))).
       2 : { rewrite sum_f_reindex' with (s := 1%nat). replace (n + 1)%nat with (S n) by lia. apply sum_f_equiv; try lia. intros i H5. 
             rewrite sum_f_reindex' with (s := 1%nat). replace (n + 1)%nat with (S n) by lia. apply sum_f_equiv; try lia. intros j H6.
             assert (i - 1 >= j - 1 \/ i - 1 < j - 1)%nat as [H7 | H7] by lia.
             - assert (i - 1 <? j - 1 = false)%nat as H8. { apply nltb_ge. lia. } assert (i <? j = false)%nat as H9. { apply nltb_ge. lia. } rewrite H8, H9. reflexivity.
             - assert (i - 1 <? j - 1 = true)%nat as H8. { apply Nat.ltb_lt. lia. } assert (i <? j = true)%nat as H9. { apply Nat.ltb_lt. lia. } rewrite H8, H9. replace (h1 :: t1) with ([h1] ++ t1) by reflexivity.
               replace (h2 :: t2) with ([h2] ++ t2) by reflexivity. repeat (rewrite app_nth2; try (simpl; lia)). simpl. lra. }
      rewrite <- IH. rewrite sum_f_Si; try lia. replace (sum_f 0 (S n) (fun j : nat => if (0 =? j)%nat then 0 else (nth 0 (h1 :: t1) 0 * nth j (h2 :: t2) 0) ^ 2 - nth 0 (h1 :: t1) 0 * nth 0 (h2 :: t2) 0 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0)) with 
      (sum_f 1 (S n) (fun j : nat => (h1 * nth j (h2 :: t2) 0) ^ 2 - h1 * h2 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0)).
      2 : { rewrite sum_f_Si with (i := 0%nat); try lia. replace ((if (0 =? 0)%nat then 0 else (nth 0 (h1 :: t1) 0 * nth 0 (h2 :: t2) 0) ^ 2 - nth 0 (h1 :: t1) 0 * nth 0 (h2 :: t2) 0 * nth 0 (h1 :: t1) 0 * nth 0 (h2 :: t2) 0)) with 0 by reflexivity.
            field_simplify. apply sum_f_equiv; try lia. intros j H5. assert (0 =? j = false)%nat as H6. { compute. destruct j; lia. } rewrite H6. simpl. lra. }
      replace (S n) with (length t1) at 2 by lia. rewrite sum_f_nth_cons_4; try lia.
      replace (sum_f 1 (S n) (fun i : nat => sum_f 0 (S n) (fun j : nat => if (i =? j)%nat then 0 else (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0) ^ 2 - nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0))) with 
              (sum_f 1 (S n) (fun i : nat => (h2 * nth i (h1 :: t1) 0) ^ 2 - h2 * h1 * nth i (h2 :: t2) 0 * nth i (h1 :: t1) 0 + sum_f 1 (S n) (fun j : nat => if (i =? j)%nat then 0 else (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0) ^ 2 - nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0))).
      2 : { apply sum_f_equiv; try lia. intros i H5. rewrite sum_f_Si with (i := 0%nat); try lia. assert (i =? 0 = false)%nat as H6. { compute. destruct i; lia. } rewrite H6. simpl; lra. }
      rewrite <- sum_f_plus; try lia. replace (S n) with (length t2) at 1 by lia. rewrite sum_f_nth_cons_4; try lia. rewrite <- H3. repeat rewrite <- sum_f_minus; try lia. 
      replace ((fun i : nat => h2 * h1 * nth i t2 0 * nth i t1 0)) with ((fun i : nat => h1 * h2 * nth i t1 0 * nth i t2 0)). 2 : { apply functional_extensionality. intros i. lra. }
      replace (fun i : nat => (h1 * nth i t2 0 - h2 * nth i t1 0) ^ 2) with (fun i : nat => (h1 * nth i t2 0) ^ 2 - 2 * h1 * h2 * nth i t1 0 * nth i t2 0 + (h2 * nth i t1 0) ^ 2).
      2 : { apply functional_extensionality. intros i. lra. } rewrite <- sum_f_plus; try lia. rewrite <- sum_f_minus; try lia. 
      replace (fun i : nat => 2 * h1 * h2 * nth i t1 0 * nth i t2 0) with (fun i : nat => h1 * h2 * nth i t1 0 * nth i t2 0 + h1 * h2 * nth i t1 0 * nth i t2 0). 2 : { apply functional_extensionality. intros i. lra. }
      rewrite <- sum_f_plus; try lia. field_simplify. 
      replace (sum_f 1 (S n) (fun i : nat => sum_f 1 (S n) (fun j : nat => if (i =? j)%nat then 0 else (nth i (h1 :: t1) 0 * nth j (h2 :: t2) 0) ^ 2 - nth i (h1 :: t1) 0 * nth i (h2 :: t2) 0 * nth j (h1 :: t1) 0 * nth j (h2 :: t2) 0))) with 
              (sum_f 0 n (fun i : nat => sum_f 0 n (fun j : nat => if (i =? j)%nat then 0 else (nth i t1 0 * nth j t2 0) ^ 2 - nth i t1 0 * nth i t2 0 * nth j t1 0 * nth j t2 0))).
      2 : { rewrite sum_f_reindex' with (s := 1%nat). replace (n + 1)%nat with (S n) by lia. apply sum_f_equiv; try lia. intros i H5. rewrite sum_f_reindex' with (s := 1%nat). replace (n + 1)%nat with (S n) by lia. apply sum_f_equiv; try lia. intros j H6.
            assert (i - 1 = j - 1 \/ i - 1 <> j - 1)%nat as [H7 | H7] by lia.
            - assert (i = j) as H8 by lia. apply Nat.eqb_eq in H7, H8. rewrite H7, H8. reflexivity.
            - assert (i <> j) as H8 by lia. apply Nat.eqb_neq in H7, H8. rewrite H7, H8. replace (h1 :: t1) with ([h1] ++ t1) by reflexivity.
              replace (h2 :: t2) with ([h2] ++ t2) by reflexivity. repeat (rewrite app_nth2; try (simpl; lia)). simpl. lra. }
      lra.
Qed.

Lemma lemma_2_21_c_helper4 : forall (l1 l2 : list R),
  (length l1 = length l2)%nat -> sum_f 0 (length l1 - 1) (fun i => nth i l1 0 ^ 2) * sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2) = sum_f 0 (length l1 - 1) (fun i => nth i l1 0 * nth i l2 0) ^ 2 + sum_f 0 (length l1 - 1) (fun i => sum_f 0 (length l1 - 1) (fun j => if (i <? j)%nat then (nth i l1 0 * nth j l2 0 - nth j l1 0 * nth i l2 0) ^ 2 else 0)).
Proof.
  intros l1 l2 H1. pose proof (lemma_2_21_c_helper1 l1 l2 H1) as H2. pose proof (lemma_2_21_c_helper2 l1 l2 H1) as H3. pose proof (lemma_2_21_c_helper3 l1 l2 H1) as H4. 
  set (n := (length l1 - 1)%nat). replace (length l1 - 1)%nat with n in *; auto.
  assert (H5 : sum_f 0 (n) (fun i : nat => nth i l1 0 ^ 2) * sum_f 0 (n) (fun i : nat => nth i l2 0 ^ 2) - sum_f 0 (n) (fun i : nat => nth i l1 0 * nth i l2 0) ^ 2 = sum_f 0 (n) (fun i : nat => sum_f 0 (n) (fun j : nat => if (i =? j)%nat then 0 else (nth i l1 0 * nth j l2 0) ^ 2)) - sum_f 0 (n) (fun i : nat => sum_f 0 (n) (fun j : nat => if (i =? j)%nat then 0 else nth i l1 0 * nth i l2 0 * nth j l1 0 * nth j l2 0))).
  { rewrite H2, H3. lra. } rewrite sum_f_minus in H5; try lia. rewrite <- H4. apply Rplus_eq_compat_r with (r := sum_f 0 n (fun i : nat => nth i l1 0 * nth i l2 0) ^ 2) in H5.
  field_simplify in H5. rewrite H5. apply Rminus_eq_reg_r with (r := sum_f 0 n (fun i : nat => nth i l1 0 * nth i l2 0) ^ 2). field_simplify.
  apply sum_f_equiv; try lia. intros k H6. rewrite sum_f_minus; try lia. apply sum_f_equiv; try lia. intros j H7. assert (k = j \/ k <> j)%nat as [H8 | H8] by lia.
  - assert (k =? j = true)%nat as H9 by (apply Nat.eqb_eq; lia). rewrite H9. lra.
  - assert (k =? j = false)%nat as H9 by (apply Nat.eqb_neq; lia). rewrite H9. lra.
Qed.

Lemma lemma_2_21_c : forall (l1 l2 : list R),
  (length l1 = length l2)%nat -> sum_f 0 (length l1 - 1) (fun i => nth i l1 0 * nth i l2 0) <= sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l1 0 ^ 2)) * sqrt (sum_f 0 (length l1 - 1) (fun i => nth i l2 0 ^ 2)).
Proof.
  intros l1 l2 H1. pose proof (lemma_2_21_c_helper4 l1 l2 H1) as H2. rewrite <- sqrt_mult_alt.
  2 : { apply sum_f_nonneg; try lia. intros i H3. apply pow2_ge_0. }
  apply Rsqr_incr_0_var; try apply sqrt_pos. repeat rewrite Rsqr_pow2. rewrite pow2_sqrt. 2 : { apply Rmult_le_pos; repeat (apply sum_f_nonneg; try lia; intros i H3; apply pow2_ge_0). }
  assert (0 <= sum_f 0 (length l1 - 1) (fun i : nat => sum_f 0 (length l1 - 1) (fun j : nat => if (i <? j)%nat then (nth i l1 0 * nth j l2 0 - nth j l1 0 * nth i l2 0) ^ 2 else 0))).
  { apply sum_f_nonneg; try lia. intros i H3. apply sum_f_nonneg; try lia. intros j H4. assert (i < j \/ i >= j)%nat as [H5 | H5] by lia.
    - assert (i <? j = true)%nat as H6 by (apply Nat.ltb_lt; lia). rewrite H6. apply pow2_ge_0.
    - assert (i <? j = false)%nat as H6 by (apply Nat.ltb_ge; lia). rewrite H6. lra. 
  } lra.
Qed.

Definition prod_f (s n : nat) (f:nat -> R) : R :=
  prod_f_R0 (fun x:nat => f (x + s)%nat) (n - s).

Lemma prod_f_n_n : forall n f,
  prod_f n n f = f n.
Proof.
  intros n f. unfold prod_f. replace (n - n)%nat with 0%nat by lia.
  simpl. reflexivity. 
Qed.

Definition pos_list (l : list R) : Prop :=
  Forall (fun x => x > 0) l.

Definition arithmetic_mean (l : list R) : R :=
  fold_right Rplus 0 l / INR (length l).

Definition arithmetic_mean_prime (l : list R) : R :=
  sum_f 0 (length l - 1) (fun i => nth i l 0) / INR (length l).

Definition geometric_mean (l : list R) : R :=
  if eq_nat_dec (length l) 0 then 0 else
  Rpower (fold_right Rmult 1 l) (1 / INR (length l)).

Lemma pos_list_cons : forall h l,
  pos_list (h :: l) <-> h > 0 /\ pos_list l.
Proof.
  intros h l. split.
  - intros H1. unfold pos_list in H1. apply Forall_cons_iff in H1. tauto.
  - intros [H1 H2]. unfold pos_list. rewrite Forall_forall. intros x [H3 | H4].
    -- rewrite <- H3; auto.
    -- unfold pos_list in H2. rewrite Forall_forall in H2. specialize (H2 x H4); auto.
Qed.

Lemma pos_list_app_iff : forall l1 l2,
  pos_list (l1 ++ l2) <-> pos_list l1 /\ pos_list l2.
Proof.
  intros l1 l2. split.
  - intros H1. unfold pos_list in H1. apply Forall_app in H1 as [H1 H1']. tauto.
  - intros [H1 H2]. unfold pos_list. apply Forall_app. tauto.
Qed.

Lemma fold_right_mult_pos_list_gt_0 : forall l,
  pos_list l -> fold_right Rmult 1 l > 0.
Proof.
  intros l H1. induction l as [| h l' IH].
  - simpl. lra.
  - simpl. apply pos_list_cons in H1 as [H1 H2]. apply IH in H2. nra.
Qed.

Lemma fold_right_plus_pos_list_gt_0 : forall l,
  pos_list l -> (length l > 0)%nat -> fold_right Rplus 0 l > 0.
Proof.
  intros l H1 H2. induction l as [| h l' IH].
  - simpl in H2. lia.
  - simpl. destruct l'.
    -- simpl in *. apply pos_list_cons in H1 as [H1 H3]. nra.
    -- apply pos_list_cons in H1 as [H1 H3]. apply IH in H3. nra. simpl. lia.
Qed.

Lemma fold_right_mul_initial_val : forall l a,
  fold_right Rmult a l = a * fold_right Rmult 1 l.
Proof.
  intros l a. induction l as [| h l' IH].
  - simpl. lra.
  - simpl. rewrite IH. lra.
Qed.

Lemma ge_le_arith_2 : forall a b,
  a > 0 -> b > 0 -> sqrt (a * b) <= (a + b) / 2.
Proof.
  intros a b H1 H2. apply Rmult_le_reg_r with (r := 2). lra.
  replace ((a + b) / 2 * 2) with (a + b) by lra. rewrite sqrt_mult; try lra.
  apply Rsqr_incr_0_var. 2 : { lra. } unfold Rsqr.
  replace (sqrt a * sqrt b * 2 * (sqrt a * sqrt b * 2)) with (4 * (sqrt a * sqrt a) * (sqrt b * sqrt b)) by lra.
  repeat rewrite sqrt_sqrt; try lra. replace ((a + b) * (a + b)) with (a * a + 2 * a * b + b * b) by lra.
  pose proof (Rtotal_order a b) as [H3 | [H4 | H5]]; try nra.
Qed.

Lemma geometric_mean_app : forall l1 l2,
  pos_list l1 -> pos_list l2 -> length l1 = length l2 ->
  geometric_mean (l1 ++ l2) = sqrt (geometric_mean l1 * geometric_mean l2).
Proof.
  intros l1 l2 H1 H2 H3. unfold geometric_mean. rewrite H3. destruct l1, l2.
  - simpl. rewrite Rmult_0_r. rewrite sqrt_0. reflexivity.
  - simpl in H3; lia.
  - simpl in H3; lia.
  - simpl in *. pose proof H3 as H3'. destruct (length l2) in H3. 
    -- assert (H4 : l1 = []). { destruct l1. reflexivity. simpl in H3. lia. } rewrite H4. simpl. rewrite Rmult_1_r. assert (length l2 = 0%nat). { destruct l2. auto. inversion H3'. apply length_zero_iff_nil in H4. lia. }
       rewrite H. replace (1 / (1 + 1)) with (/ 2) by nra. replace (1 / 1) with 1 by lra. rewrite Rpower_mult_distr. 2 : { apply pos_list_cons in H1. tauto. }
       2 : { assert (fold_right Rmult 1 l2 > 0). { apply pos_list_cons in H2. apply fold_right_mult_pos_list_gt_0; tauto. } apply pos_list_cons in H2. nra. }
       rewrite Rpower_sqrt. 2 : { apply pos_list_cons in H1 as [H1 H1']. apply pos_list_cons in H2 as [H2 H2']. assert (fold_right Rmult 1 l2 > 0) by (apply fold_right_mult_pos_list_gt_0; tauto).
       assert (r0 * fold_right Rmult 1 l2 > 0) by nra. nra. }
       rewrite Rpower_1. 2 : { apply pos_list_cons in H1 as [H1 H1']. apply pos_list_cons in H2 as [H2 H2']. assert (fold_right Rmult 1 l2 > 0) by (apply fold_right_mult_pos_list_gt_0; tauto).
       assert (r0 * fold_right Rmult 1 l2 > 0) by nra. nra. }
       reflexivity.
    -- assert (H4 : length (l1 ++ r0 :: l2) = S (S (S (n + n)))).
        { replace (S (S (S (n + n)))) with (S n + S n + 1)%nat by lia. inversion H3. inversion H0. rewrite app_length. simpl. lia. }
        destruct (length (l1 ++ r0 :: l2)). lia. destruct (length l2). lia. assert (H5 : r * fold_right Rmult 1 l1 > 0). { apply pos_list_cons in H1. assert (fold_right Rmult 1 l1 > 0) by (apply fold_right_mult_pos_list_gt_0; tauto). nra. }
        assert (H6 : r0 * fold_right Rmult 1 l2 > 0). { apply pos_list_cons in H2. assert (fold_right Rmult 1 l2 > 0) by (apply fold_right_mult_pos_list_gt_0; tauto). nra. } rewrite Rpower_mult_distr; auto.
        rewrite <- Rpower_sqrt. rewrite Rpower_mult. rewrite H4. inversion H4 as [H7]. replace (S n1) with (S n). 2 : { inversion H3. inversion H3'. reflexivity. } repeat rewrite S_INR. rewrite plus_INR.
        replace ((1 / (INR n + 1 + 1) * / 2)) with ((1 / (INR n + INR n + 1 + 1 + 1 + 1))). 2 : { field. split; pose proof pos_INR n; lra. }
        replace (r * fold_right Rmult 1 (l1 ++ r0 :: l2)) with (r * fold_right Rmult 1 l1 * (r0 * fold_right Rmult 1 l2)).
        2 : { rewrite fold_right_app. simpl. rewrite fold_right_mul_initial_val with (a := r0 * fold_right Rmult 1 l2). nra. }
        reflexivity.
        apply Rgt_lt. apply Rpower_gt_0. apply Rmult_gt_0_compat; auto.
Qed.

Lemma pow_2_n_gt_0 : forall n,
  (2 ^ n > 0)%nat.
Proof.
  intros n. induction n as [| k IH].
  - simpl. lia.
  - simpl. lia.
Qed.

Lemma fold_right_plus_app : forall l1 l2,
  fold_right Rplus 0 (l1 ++ l2) = fold_right Rplus 0 l1 + fold_right Rplus 0 l2.
Proof.
  intros l1 l2. induction l1 as [| h l1' IH].
  - simpl. lra.
  - simpl. rewrite IH. lra.
Qed.

Lemma fold_right_mult_app_R : forall l1 l2,
  fold_right Rmult 1 (l1 ++ l2) = fold_right Rmult 1 l1 * fold_right Rmult 1 l2.
Proof.
  intros l1 l2. induction l1 as [| h l1' IH].
  - simpl. lra.
  - simpl. rewrite IH. lra.
Qed.

Lemma sum_f_fold_right_equiv : forall (l : list R),
  sum_f 0 (length l - 1) (fun i => nth i l 0) = fold_right Rplus 0 l.
Proof.
  induction l as [| h t IH].
  - simpl. rewrite sum_f_0_0. reflexivity.
  - replace (length (h :: t) - 1)%nat with (length t) by (simpl; lia).
    replace (h :: t) with ([h] ++ t) by (reflexivity). replace (fold_right Rplus 0 ([h] ++ t)) with (h + fold_right Rplus 0 t).
    2 : { rewrite fold_right_app. reflexivity. } assert (length t = 0 \/ length t > 0)%nat as [H1 | H1] by lia.
    -- rewrite H1. rewrite sum_f_0_0. rewrite length_zero_iff_nil in H1. rewrite H1. simpl; lra.
    -- rewrite sum_f_Si; try lia. rewrite sum_f_reindex with (s := 1%nat); try lia. replace (fun x : nat => nth (x + 1) ([h] ++ t) 0) with (fun x : nat => nth x t 0).
       2 : { apply functional_extensionality. intro x. rewrite app_nth2. 2 : { simpl. lia. } simpl. replace (x + 1 - 1)%nat with x by lia. reflexivity. } 
       simpl. rewrite <- IH. lra.
Qed.

Lemma arith_mean_equiv : forall l : list R,
  arithmetic_mean l = arithmetic_mean_prime l.
Proof.
  intros l. unfold arithmetic_mean. unfold arithmetic_mean_prime.
  rewrite sum_f_fold_right_equiv. reflexivity.
Qed.

Lemma exists_nth_lt_gt_arith_mean : forall (l : list R),
  (nth 0 l 0) < arithmetic_mean l -> exists i, (0 < i < length l)%nat /\ nth i l 0 > arithmetic_mean l.
Proof.
  intros l H1. pose proof (classic (exists i, (0 < i < length l)%nat /\ nth i l 0 > arithmetic_mean l)) as [H2 | H2]; auto.
  assert (H3 : forall i, ~(0 < i < (length l))%nat \/ ~nth i l 0 > arithmetic_mean l). 
  { intro i. apply not_and_or. intro H3. apply H2. exists i. apply H3. }
  assert (H4 : forall i, (0 >= i \/ i >= length l)%nat \/ nth i l 0 <= arithmetic_mean l).
  { intro i. specialize (H3 i). destruct H3 as [H3 | H3]. left. lia. right. lra. }
  assert (H5 : forall i, (0 <= i < length l)%nat -> nth i l 0 <= arithmetic_mean l). { intros i H5. specialize (H4 i). destruct H4 as [[H4 | H4] | H4]. destruct i. apply Rlt_le. apply H1. lia. lia. auto. }
  assert (length l = 0 \/ length l > 0)%nat as [H6 | H6] by lia. apply length_zero_iff_nil in H6. rewrite H6 in H1. compute in H1; lra.
  assert (H7 : sum_f 0 (length l - 1) (fun i => nth i l 0) < arithmetic_mean l * INR (length l)).
  { replace (length l) with (length l - 1 - 0 + 1)%nat at 2 by lia. apply sum_f_lt; try lia. exists 0%nat. split. lia. auto. intros k H7. apply H5. lia. }
  unfold arithmetic_mean in H7. rewrite <- sum_f_fold_right_equiv in H7. field_simplify in H7. lra. apply not_0_INR. lia.
Qed.

Lemma fold_right_plus_repeat : forall a n,
  fold_right Rplus 0 (repeat a n) = a * INR n.
Proof.
  intros a n. induction n as [| k IH].
  - simpl. lra.
  - simpl. rewrite IH. destruct k; simpl; lra.
Qed.

Lemma fold_right_mult_repeat : forall a n,
  fold_right Rmult 1 (repeat a n) = a ^ n.
Proof.
  intros a n. induction n as [| k IH].
  - simpl. lra.
  - simpl. rewrite IH. lra.
Qed.

Lemma arithmetic_mean_repeat : forall n x,
  (n <> 0)%nat -> arithmetic_mean (repeat x n) = x.
Proof.
  intros n x H1. unfold arithmetic_mean. rewrite repeat_length. rewrite fold_right_plus_repeat. field. apply not_0_INR. lia.
Qed.

Lemma geometric_mean_repeat : forall n x,
  (n <> 0)%nat -> x > 0 -> geometric_mean (repeat x n) = x.
Proof.
  intros n x H1 H2. unfold geometric_mean. rewrite repeat_length. rewrite fold_right_mult_repeat. 
  destruct (Nat.eq_dec n 0) as [H3 | H3]; try lia. apply pow_eq_1 with (n := n); try lia; try lra. 
  apply Rpower_gt_0. apply Rpow_gt_0; auto. rewrite <- Rpower_pow. rewrite Rpower_mult.
  replace (1 / INR n * INR n) with 1 by (field; apply not_0_INR; lia). rewrite Rpower_1; auto.
  apply Rpow_gt_0; auto. apply Rpower_gt_0. apply Rpow_gt_0; auto.
Qed.

Lemma ordered_Rlist_Sorted : forall l : list R,
  ordered_Rlist l -> Sorted Rle l.
Proof.
  intros l H1. induction l as [| h t IH].
  - apply Sorted_nil.
  - constructor.
    -- apply RList_P4 in H1. apply IH. apply H1.
    -- destruct t. constructor. constructor. specialize (H1 0%nat). simpl in H1. apply H1. lia.
Qed.

Lemma ordered_Rlist_cons : forall h l,
  ordered_Rlist l -> h <= hd 0 l -> ordered_Rlist (h :: l).
Proof.
  intros h l H1 H2. replace (h :: l) with ([h] ++ l) by reflexivity. apply RList_P25; auto.
  - intros i H3. simpl in H3. lia.
  - simpl. destruct l; auto.
Qed.

Lemma Sorted_ordered_Rlist : forall l : list R,
  Sorted Rle l -> ordered_Rlist l.
Proof.
  intros l H1. induction l as [| h t IH].
  - intros i H2. simpl. lra.
  - apply Sorted_inv in H1 as [H1 H3]. apply IH in H1. destruct t.
    -- intros i H4. simpl in H4. lia.
    -- apply ordered_Rlist_cons; auto. apply HdRel_inv in H3. simpl. lra.
Qed.

Lemma insert_count_occ_eq : forall l x,
  count_occ Req_dec_T (insert l x) x = S (count_occ Req_dec_T l x).
Proof.
  intros l x. induction l as [| h t IH].
  - simpl. destruct Req_dec_T; tauto.
  - simpl. destruct Req_dec_T as [H1 | H1].
    -- simpl. rewrite <- IH. replace (if Rle_dec h x then h :: insert t x else x :: h :: t) with (h :: insert t x).
       2 : { destruct (Rle_dec h x); auto; lra. } rewrite H1. rewrite count_occ_cons_eq; auto.
    -- assert (h < x \/ h > x) as [H2 | H2] by lra.
       + rewrite <- IH. replace (if Rle_dec h x then h :: insert t x else x :: h :: t) with (h :: insert t x).
         2 : { destruct (Rle_dec h x); auto; lra. } rewrite count_occ_cons_neq; auto.
       + rewrite <- IH. replace (if Rle_dec h x then h :: insert t x else x :: h :: t) with (x :: h :: t).
         2 : { destruct (Rle_dec h x); auto; lra. } rewrite count_occ_cons_eq; auto. rewrite count_occ_cons_neq; auto.
Qed.

Lemma insert_count_occ_neq : forall l x y,
  x <> y -> count_occ Req_dec_T (insert l x) y = count_occ Req_dec_T l y.
Proof.
  intros l x y H1. induction l as [| h t IH].
  - simpl. destruct Req_dec_T; tauto.
  - simpl. destruct Req_dec_T as [H2 | H2].
    -- simpl. rewrite <- IH. assert (h < x \/ h > x) as [H3 | H3] by lra.
       + replace (if Rle_dec h x then h :: insert t x else x :: h :: t) with (h :: insert t x).
         2 : { destruct (Rle_dec h x); auto; lra. } rewrite count_occ_cons_eq; auto.
       + replace (if Rle_dec h x then h :: insert t x else x :: h :: t) with (x :: h :: t).
         2 : { destruct (Rle_dec h x); auto; lra. } rewrite count_occ_cons_neq; auto. rewrite count_occ_cons_eq; auto.
    -- assert (h <= x \/ h > x) as [H3 | H3] by lra.
       + rewrite <- IH. replace (if Rle_dec h x then h :: insert t x else x :: h :: t) with (h :: insert t x).
         2 : { destruct (Rle_dec h x); auto; lra. } rewrite count_occ_cons_neq; auto.
       + rewrite <- IH. replace (if Rle_dec h x then h :: insert t x else x :: h :: t) with (x :: h :: t).
         2 : { destruct (Rle_dec h x); auto; lra. } rewrite count_occ_cons_neq; auto. rewrite count_occ_cons_neq; auto.
Qed.

Lemma exists_sorted_list_R : forall l1 : list R,
  exists l2 : list R, Sorted Rle l2 /\ Permutation l1 l2.
Proof.
  induction l1 as [| h t IH].
  - exists []. split. apply Sorted_nil. apply Permutation_refl.
  - destruct IH as [l3 [H1 H2]]. assert (length l3 = 0 \/ length l3 = 1 \/ length l3 >= 2)%nat as [H3 | [H3 | H3]] by lia.
    -- apply length_zero_iff_nil in H3. rewrite H3 in *. exists [h]. split. apply Sorted_cons; auto. apply Permutation_sym in H2. 
       apply Permutation_nil in H2. rewrite H2. apply Permutation_refl.
    -- assert (h <= hd 0 l3 \/ h > hd 0 l3) as [H4 | H4] by lra.
       + exists (h :: l3); split. apply Sorted_cons; auto. destruct l3. pose proof (length_zero_iff_nil ([] : list R)); auto.
         constructor. simpl in H4. lra. apply Permutation_cons; auto.
       + exists (l3 ++ [h]); split. destruct l3. simpl. pose proof (length_zero_iff_nil ([] : list R)); auto. assert (l3 = []) as H5.
         { simpl in H3. inversion H3 as [H5]. apply length_zero_iff_nil in H5; auto. } rewrite H5. apply Sorted_cons; auto. constructor. simpl in H4. lra.
          apply Permutation_cons_app; auto. rewrite app_nil_r. auto.
    -- exists (insert l3 h); split. apply ordered_Rlist_Sorted. apply RList_P1. apply Sorted_ordered_Rlist; auto. rewrite (Permutation_count_occ Req_dec_T). intros x.
       assert (x = h \/ x <> h) as [H4 | H4] by lra. rewrite H4. rewrite count_occ_cons_eq; auto. rewrite insert_count_occ_eq. rewrite (Permutation_count_occ Req_dec_T) in H2.
       specialize (H2 x). rewrite H4 in H2. rewrite H2. reflexivity. rewrite count_occ_cons_neq; auto. rewrite insert_count_occ_neq; auto. rewrite (Permutation_count_occ Req_dec_T) in H2.
       specialize (H2 x). rewrite H2. reflexivity.        
Qed.

Lemma sum_f_Permutation : forall l1 l2,
  Permutation l1 l2 -> sum_f 0 (length l1 - 1) (fun i => nth i l1 0) = sum_f 0 (length l2 - 1) (fun i => nth i l2 0).
Proof.
  intros l1 l2 H1. rewrite (Permutation_count_occ Req_dec_T) in H1. repeat rewrite sum_f_fold_right_equiv. apply count_occ_eq_sum_right_prime.
  apply functional_extensionality. apply H1.
Qed.

Lemma fold_right_Rmult_Permutation : forall l1 l2,
  Permutation l1 l2 -> fold_right Rmult 1 l1 = fold_right Rmult 1 l2.
Proof.
  intros l1 l2 H1. rewrite (Permutation_count_occ Req_dec_T) in H1. apply count_occ_eq_prod_right_prime.
  apply functional_extensionality. apply H1.
Qed.

Lemma arithmetic_mean_all_equal : forall (l : list R) r,
  (length l > 0)%nat -> Forall (fun x => x = r) l -> arithmetic_mean l = r.
Proof.
  intros l r H1 H2. rewrite arith_mean_equiv. unfold arithmetic_mean_prime. rewrite Forall_forall in H2.
  replace (sum_f 0 (length l - 1) (fun i : nat => nth i l 0)) with (sum_f 0 (length l - 1) (fun _ => r)).
  2 : { 
        apply sum_f_equiv; try lia. intros i H3. rewrite H2; try lra. assert (i < length l \/ i >= length l)%nat as [H4 | H4] by lia.
        apply nth_In; lia. lia.
      }
  rewrite sum_f_const. replace (length l - 1 - 0 + 1)%nat with (length l) by lia. field. apply not_0_INR. lia.
Qed.

Lemma arith_mean_Permtation_eq : forall l1 l2,
  Permutation l1 l2 -> arithmetic_mean l1 = arithmetic_mean l2.
Proof.
  intros l1 l2 H1. assert (length l1 = length l2) as H2. { apply Permutation_length; auto. }
  assert (length l1 = 0 \/ length l1 > 0)%nat as [H3 | H3] by lia.
  - rewrite H3 in H2. apply eq_sym in H2. apply length_zero_iff_nil in H2, H3. rewrite H2, H3. reflexivity.
  - assert (length l2 > 0)%nat as H4 by lia. 
    repeat rewrite arith_mean_equiv. unfold arithmetic_mean_prime. rewrite H2. apply Rmult_eq_reg_r with (r := INR (length l2)).
    2 : { apply Rgt_not_eq. apply lt_0_INR; lia. } field_simplify; try (apply not_0_INR; lia). rewrite <- H2 at 1.
    apply sum_f_Permutation; auto.
Qed.

Lemma fold_right_Rmult_const : forall (l : list R) r,
  (forall x, In x l -> x = r) ->
  fold_right Rmult 1 l = r ^ (length l).
Proof.
  intros l r H1. induction l as [| h t IH].
  - simpl. lra.
  - simpl. rewrite IH. 2 : { intros x H2. apply H1. right. auto. } replace h with r.
    2 : { rewrite H1; auto. left. reflexivity. } lra.
Qed.

Lemma geometric_mean_all_equal : forall (l : list R) r,
  (length l > 0)%nat -> pos_list l -> Forall (fun x => x = r) l -> geometric_mean l = r.
Proof.
  intros l r H1 H2 H3. unfold geometric_mean. destruct (eq_nat_dec (length l) 0) as [H4 | H4]; try lia.
  rewrite Forall_forall in H3. rewrite fold_right_Rmult_const with (r := r); auto.
  assert (0 < r) as H5. { unfold pos_list in H2. rewrite Forall_forall in H2. apply H2. destruct l. simpl in H1. lia. left. apply H3. left. auto. }
  rewrite <- Rpower_pow; auto. rewrite Rpower_mult. replace (INR (length l) * (1 / INR (length l))) with 1. 2 : { field. apply not_0_INR. lia. }
  rewrite Rpower_1; auto.
Qed.

Lemma MinRlist_cons : forall h t,
  (length t > 0)%nat -> MinRlist (h :: t) = Rmin h (MinRlist t).
Proof.
  intros h t H1. destruct t.
  - simpl in H1. lia.
  - reflexivity.
Qed.

Lemma MaxRlist_cons : forall h t,
  (length t > 0)%nat -> MaxRlist (h :: t) = Rmax h (MaxRlist t).
Proof.
  intros h t H1. destruct t.
  - simpl in H1. lia.
  - reflexivity.
Qed.

Lemma MinRlist_In : forall l,
  (length l > 0)%nat -> In (MinRlist l) l.
Proof.
  intros l H1. induction l as [| h t IH].
  - simpl in H1. lia.
  - assert (length t = 0 \/ length t > 0)%nat as [H2 | H2] by lia.
    -- apply length_zero_iff_nil in H2. rewrite H2. simpl. left. reflexivity.
    -- pose proof H2 as H3. apply IH in H2. destruct (Rle_dec h (MinRlist t)) as [H4 | H4].
       + left. rewrite MinRlist_cons; auto. unfold Rmin; destruct (Rle_dec h (MinRlist t)); lra.
       + right. rewrite MinRlist_cons; auto. assert (H5 : h > MinRlist t) by lra. unfold Rmin. destruct (Rle_dec h (MinRlist t)); try lra. apply IH. auto.
Qed.

Lemma MaxRlist_In : forall l,
  (length l > 0)%nat -> In (MaxRlist l) l.
Proof.
  intros l H1. induction l as [| h t IH].
  - simpl in H1. lia.
  - assert (length t = 0 \/ length t > 0)%nat as [H2 | H2] by lia.
    -- apply length_zero_iff_nil in H2. rewrite H2. simpl. left. reflexivity.
    -- pose proof H2 as H3. apply IH in H2. destruct (Rle_dec h (MaxRlist t)) as [H4 | H4].
       + right. rewrite MaxRlist_cons; auto. assert (H5 : h <= MaxRlist t) by lra. unfold Rmax. destruct (Rle_dec h (MaxRlist t)); try lra. apply IH. auto.
       + left. rewrite MaxRlist_cons; auto. unfold Rmax. destruct (Rle_dec h (MaxRlist t)); lra.
Qed.

Lemma nth_pos_Rl : forall l i,
  nth i l 0 = pos_Rl l i.
Proof.
  intros l i. generalize dependent i. induction l as [| h t IH].
  - destruct i; reflexivity.
  - intros i. destruct i.
    -- reflexivity.
    -- simpl. apply IH.
Qed.

Lemma Sorted_MinRlist : forall l,
  Sorted Rle l -> (length l > 0)%nat -> MinRlist l = nth 0 l 0.
Proof.
  intros l H1 H2. assert (H3 : In (MinRlist l) l) by (apply MinRlist_In; auto). apply Sorted_ordered_Rlist in H1.
  assert (H4 : In (nth 0 l 0) l). { apply nth_In. lia. } pose proof (MinRlist_P1 l (nth 0 l 0) H4) as H5.
  pose proof (RList_P5 l (MinRlist l) H1 H3) as H6. rewrite nth_pos_Rl in *. lra.
Qed.

Lemma Sorted_MaxRlist : forall l,
  Sorted Rle l -> (length l > 0)%nat -> MaxRlist l = nth (length l - 1) l 0.
Proof.
  intros l H1 H2. assert (H3 : In (MaxRlist l) l) by (apply MaxRlist_In; auto). apply Sorted_ordered_Rlist in H1.
  assert (H4 : In (nth (length l - 1) l 0) l). { apply nth_In. lia. } pose proof (MaxRlist_P1 l (nth (length l - 1) l 0) H4) as H5.
  pose proof (RList_P7 l (MaxRlist l) H1 H3) as H6. rewrite nth_pos_Rl in *. replace (Init.Nat.pred (length l)) with (length l - 1)%nat in H6 by lia. lra.
Qed.

Lemma Sorted_tail_unique : forall l,
  Sorted Rle l -> (length l > 0)%nat -> (~Forall (fun x => x = nth 0 l 0) l) -> nth 0 l 0 < nth (length l - 1) l 0.
Proof.
  intros l H1 H2 H3. assert (H4 : In (nth 0 l 0) l) by (apply nth_In; lia). assert (H5 : In (nth (length l - 1) l 0) l) by (apply nth_In; lia).
  pose proof (Sorted_MinRlist l H1 H2) as H6.  pose proof (Sorted_MaxRlist l H1 H2) as H7. apply neg_Forall_Exists_neg in H3. 2 : { intros x. apply Req_dec_T. } 
  apply Sorted_ordered_Rlist in H1. pose proof (RList_P7  l (nth 0 l 0) H1 H4) as H8. replace (Init.Nat.pred (length l)) with (length l - 1)%nat in H8 by lia. 
  destruct H8 as [H8 | H8].
  - rewrite <- nth_pos_Rl in H8. lra.
  - rewrite <- nth_pos_Rl in H8. apply Exists_exists in H3 as [x [H3 H9]]. pose proof (Rtotal_order (nth (length l - 1) l 0) x) as [H10 | [H10 | H10]]; try lra.
    -- pose proof (MaxRlist_P1 l x H3) as H11. lra.
    -- pose proof (MaxRlist_P1 l x H3) as H11. pose proof (MinRlist_P1 l x H3); lra.
Qed.

Lemma MinElementLessThanMean : forall (l : list R),
  ~Forall (fun x => x = nth 0 l 0) l -> (length l > 0)%nat -> Sorted Rle l -> nth 0 l 0 < arithmetic_mean l.
Proof.
  intros l H1 H2 H3. assert (nth 0 l 0 = MinRlist l) as H4. { rewrite nth_pos_Rl. rewrite Sorted_MinRlist; auto. rewrite nth_pos_Rl. reflexivity. }
  pose proof (Sorted_tail_unique l H3 H2 H1) as H5. rewrite arith_mean_equiv. unfold arithmetic_mean_prime. apply Rmult_lt_reg_r with (r := INR (length l)).
  apply lt_0_INR; lia. field_simplify. 2 : { apply not_0_INR. lia. } assert (H6 : (length l > 1)%nat).
  { assert (length l = 1 \/ length l > 1)%nat as [H6 | H6] by lia. rewrite H6 in H5. simpl in H5. lra. lia. }
  replace (length l - 1)%nat with (S (length l - 2)) by lia. rewrite sum_f_i_Sn_f; try lia. replace (S (length l - 2)) with (length l - 1)%nat by lia.
  assert (nth 0 l 0 * INR (length l - 2 - 0 + 1) <= sum_f 0 (length l - 2) (fun i => nth i l 0)) as H7.
  { rewrite <- sum_f_const. apply sum_f_congruence_le; try lia. intros i H7. assert (In (nth i l 0) l) as H8. { apply nth_In. lia. } 
    pose proof (MinRlist_P1 l (nth i l 0) H8) as H9. lra. }
  replace (length l - 2 - 0 + 1)%nat with (length l - 1)%nat in H7 by lia. replace (length l) with (length l - 1 + 1)%nat at 1 by lia.
  rewrite plus_INR. rewrite Rmult_plus_distr_l. rewrite Rmult_1_r. apply Rplus_le_lt_compat; lra.
Qed.

Lemma MaxElementGreaterThanMean : forall (l : list R),
  ~Forall (fun x => x = nth 0 l 0) l -> (length l > 0)%nat -> Sorted Rle l -> nth (length l - 1) l 0 > arithmetic_mean l.
Proof.
  intros l H1 H2 H3. assert (nth (length l - 1) l 0 = MaxRlist l) as H4. { rewrite nth_pos_Rl. rewrite Sorted_MaxRlist; auto. rewrite nth_pos_Rl. reflexivity. }
  pose proof (Sorted_tail_unique l H3 H2 H1) as H5. rewrite arith_mean_equiv. unfold arithmetic_mean_prime. apply Rmult_lt_reg_r with (r := INR (length l)).
  apply lt_0_INR; lia. field_simplify. 2 : { apply not_0_INR. lia. } assert (H6 : (length l > 1)%nat).
  { assert (length l = 1 \/ length l > 1)%nat as [H6 | H6] by lia. rewrite H6 in H5. simpl in H5. lra. lia. }
  replace (length l - 1)%nat with (S (length l - 2)) by lia. rewrite sum_f_Si; try lia.
  assert (nth (length l - 1) l 0 * INR (length l - 2 - 0 + 1) >= sum_f 1 (length l - 1) (fun i => nth i l 0)) as H7.
  { rewrite <- sum_f_const. apply Rle_ge. rewrite sum_f_reindex with (s := 1%nat); try lia. replace (length l - 1 - 1)%nat with (length l - 2)%nat by lia.
  apply sum_f_congruence_le; try lia. intros i H7. assert (In (nth (i+1) l 0) l) as H8. { apply nth_In. lia. } 
    pose proof (MaxRlist_P1 l (nth (i+1) l 0) H8) as H9. lra. }
  replace (length l - 2 - 0 + 1)%nat with (length l - 1)%nat in H7 by lia. replace (S (length l - 2)) with (length l - 1)%nat by lia.
  replace (length l) with (length l - 1 + 1)%nat at 2 by lia.
  rewrite plus_INR. rewrite Rmult_plus_distr_r. rewrite Rmult_1_l. apply Rlt_gt. apply Rplus_le_lt_compat; try lra.
Qed.

Lemma MinRlist_eq_MaxRlist : forall l,
  (length l > 0)%nat -> MinRlist l = MaxRlist l -> Forall (fun x => x = nth 0 l 0) l.
Proof.
  intros l H1 H2. apply Forall_forall. intros x H3. specialize (MinRlist_P1 l x H3) as H4. specialize (MaxRlist_P1 l x H3) as H5.
  assert (H6 : In (nth 0 l 0) l). { apply nth_In. lia. } pose proof (MinRlist_P1 l (nth 0 l 0) H6) as H7. pose proof (MaxRlist_P1 l (nth 0 l 0) H6) as H8.
  lra.
Qed.

Lemma Forall_eq_imp_eq_nth : forall l i,
  (i < length l)%nat ->
  Forall (fun x => x = nth i l 0) l <-> (forall x, In x l -> Forall (eq x) l).
Proof.
  intros l i H1. split.
  - intros H2. intros x H3. rewrite Forall_forall. intros y H4. rewrite Forall_forall in H2. specialize (H2 y H4) as H5. specialize (H2 x H3) as H6. lra.
  - intros H2. rewrite Forall_forall. intros y H3. specialize (H2 y H3) as H4. specialize (H2 (nth i l 0)).
    assert (H5 : In (nth i l 0) l) by (apply nth_In; auto). apply H2 in H5. rewrite Forall_forall in H4, H5. apply H4.
    apply nth_In; auto.
Qed.

Lemma Max_Permutation : forall l1 l2,
  Permutation l1 l2 -> MaxRlist l1 = MaxRlist l2.
Proof.
  intros l1 l2 H1. assert (length l1 = 0 \/ length l1 > 0)%nat as [H2 | H2] by lia.
  - apply length_zero_iff_nil in H2. rewrite H2 in H1. apply Permutation_nil in H1. rewrite H1, H2. simpl. reflexivity.
  -  assert (length l2 > 0)%nat as H4. { rewrite Permutation_length with (l' := l1); auto. apply Permutation_sym; auto. } rewrite (Permutation_count_occ Req_dec_T) in H1.
     assert (H5 : In (MaxRlist l1) l1) by (apply MaxRlist_In; auto).
     assert (H6 : In (MaxRlist l2) l2) by (apply MaxRlist_In; auto). pose proof (count_occ_In Req_dec_T l2 (MaxRlist l2)) as [H7 H8].
     pose proof (count_occ_In Req_dec_T l1 (MaxRlist l1)) as [H9 H10]. pose proof (Rtotal_order (MaxRlist l1) (MaxRlist l2)) as [H11 | [H11 | H11]]; try lra.
     -- pose proof (H1 (MaxRlist l1)) as H12. pose proof (H1 (MaxRlist l2)) as H13. assert (In (MaxRlist l1) l2) as H14.
        { apply (count_occ_In Req_dec_T). rewrite <- H12. auto. } assert (In (MaxRlist l2) l1) as H15.
        { apply (count_occ_In Req_dec_T). rewrite H13. auto. } pose proof (MaxRlist_P1 l1 (MaxRlist l2) H15) as H16. lra.
     -- pose proof (H1 (MaxRlist l1)) as H12. pose proof (H1 (MaxRlist l2)) as H13. assert (In (MaxRlist l1) l2) as H14.
        { apply (count_occ_In Req_dec_T). rewrite <- H12. auto. } assert (In (MaxRlist l2) l1) as H15.
        { apply (count_occ_In Req_dec_T). rewrite H13. auto. } pose proof (MaxRlist_P1 l2 (MaxRlist l1) H14) as H16. lra.
Qed.

Lemma Min_Permutation : forall l1 l2,
  Permutation l1 l2 -> MinRlist l1 = MinRlist l2.
Proof.
  intros l1 l2 H1. assert (length l1 = 0 \/ length l1 > 0)%nat as [H2 | H2] by lia.
  - apply length_zero_iff_nil in H2. rewrite H2 in H1. apply Permutation_nil in H1. rewrite H1, H2. simpl. reflexivity.
  -  assert (length l2 > 0)%nat as H4. { rewrite Permutation_length with (l' := l1); auto. apply Permutation_sym; auto. } rewrite (Permutation_count_occ Req_dec_T) in H1.
     assert (H5 : In (MinRlist l1) l1) by (apply MinRlist_In; auto).
     assert (H6 : In (MinRlist l2) l2) by (apply MinRlist_In; auto). pose proof (count_occ_In Req_dec_T l2 (MinRlist l2)) as [H7 H8].
     pose proof (count_occ_In Req_dec_T l1 (MinRlist l1)) as [H9 H10]. pose proof (Rtotal_order (MinRlist l1) (MinRlist l2)) as [H11 | [H11 | H11]]; try lra.
     -- pose proof (H1 (MinRlist l1)) as H12. pose proof (H1 (MinRlist l2)) as H13. assert (In (MinRlist l1) l2) as H14.
        { apply (count_occ_In Req_dec_T). rewrite <- H12. auto. } pose proof (MinRlist_P1 l2 (MinRlist l1) H14) as H16. lra.
     -- pose proof (H1 (MinRlist l1)) as H12. pose proof (H1 (MinRlist l2)) as H13. assert (In (MinRlist l1) l2) as H14.
        { apply (count_occ_In Req_dec_T). rewrite <- H12. auto. } assert (In (MinRlist l2) l1) as H15.
        { apply (count_occ_In Req_dec_T). rewrite H13. auto. } pose proof (MinRlist_P1 l1 (MinRlist l2) H15) as H16. lra.
Qed.

Lemma elementLessThanMean : forall (l : list R),
  ~Forall (fun x => x = nth 0 l 0) l -> (length l > 0)%nat -> exists i, (0 <= i < length l)%nat -> nth i l 0 < arithmetic_mean l.
Proof.
  intros l H1 H2. rewrite arith_mean_equiv. unfold arithmetic_mean_prime. pose proof (exists_sorted_list_R l) as [l' [H3 H4]].
  rewrite sum_f_Permutation with (l2 := l'); auto. assert (H5 : In (nth 0 l' 0) l'). { apply nth_In. apply Permutation_length in H4. lia. }
  pose proof (Permutation_in _ (Permutation_sym H4) H5) as H6. apply In_nth with (d := 0) in H6 as [i [H7 H8]]. exists i. intro H9.
  assert (H10 : length l = length l'). { apply Permutation_length. auto. } rewrite H10 in H7. rewrite H8. rewrite H10.
  replace (sum_f 0 (length l' - 1) (fun i0 : nat => nth i0 l' 0) / INR (length l')) with (arithmetic_mean l').
  2 : { rewrite arith_mean_equiv. unfold arithmetic_mean_prime. reflexivity. } apply MinElementLessThanMean; auto; try lia.
  intros H11. apply H1. apply MinRlist_eq_MaxRlist; try lia. rewrite Forall_forall in H11. specialize (H11 (MaxRlist l')).
  assert (length l' > 0)%nat as H12 by lia. specialize (H11 (MaxRlist_In l' H12)). pose proof (Sorted_MinRlist l' H3 H12) as H13.
  rewrite Min_Permutation with (l2 := l'); auto. rewrite Max_Permutation with (l2 := l'); auto. lra. 
Qed.

Fixpoint MinRlist_index (l : list R) : nat := 
  let min := MinRlist l in
  match l with
  | [] => 0%nat
  | h :: t => match Req_dec_T h min with 
              | left _ => 0%nat
              | right _ => S (MinRlist_index t)
              end
  end.

Fixpoint MaxRlist_index (l : list R) : nat := 
  let max := MaxRlist l in
  match l with
  | [] => 0%nat
  | h :: t => match Req_dec_T h max with 
              | left _ => 0%nat
              | right _ => S (MaxRlist_index t)
              end
  end.

Lemma MinRlist_index_cons : forall h t,
  (length t > 0)%nat -> MinRlist_index (h :: t) = if Req_dec_T h (MinRlist (h :: t)) then 0%nat else S (MinRlist_index t).
Proof.
  intros h t H1. simpl. destruct (Req_dec_T h (MinRlist (h :: t))); reflexivity.
Qed.

Lemma MaxRlist_index_cons : forall h t,
  (length t > 0)%nat -> MaxRlist_index (h :: t) = if Req_dec_T h (MaxRlist (h :: t)) then 0%nat else S (MaxRlist_index t).
Proof.
  intros h t H1. simpl. destruct (Req_dec_T h (MinRlist (h :: t))); reflexivity.
Qed.

Lemma Rmin_neq_r : forall r1 r2,
  r1 <> Rmin r1 r2 -> r2 < r1.
Proof.
  intros r1 r2 H1. unfold Rmin in H1. destruct (Rle_dec r1 r2); lra.
Qed.

Lemma Rmax_neq_r : forall r1 r2,
  r1 <> Rmax r1 r2 -> r2 > r1.
Proof.
  intros r1 r2 H1. unfold Rmax in H1. destruct (Rle_dec r1 r2); lra.
Qed.

Lemma MinRlst_index_correct : forall l,
  (length l > 0)%nat -> MinRlist l = nth (MinRlist_index l) l 0.
Proof.
  intros l H1. induction l as [| h t IH].
  - inversion H1.
  - assert (length t = 0 \/ length t > 0)%nat as [H2 | H2] by lia.
    -- apply length_zero_iff_nil in H2. rewrite H2. simpl. destruct (Req_dec_T h h) as [H3 | H3]; lra.
    -- specialize (IH H2). rewrite MinRlist_cons; auto. rewrite MinRlist_index_cons; auto. destruct (Req_dec_T h (MinRlist (h :: t))) as [H3 | H3].
       + simpl. rewrite MinRlist_cons in H3; auto.
       + simpl. rewrite MinRlist_cons in H3; auto. rewrite <- IH. pose proof (Rmin_neq_r h (MinRlist t) H3) as H4. unfold Rmin.
         destruct (Rle_dec h (MinRlist t)); lra.
Qed.

Lemma MaxRlist_index_correct : forall l, 
  (length l > 0)%nat -> MaxRlist l = nth (MaxRlist_index l) l 0.
Proof.
  intros l H1. induction l as [| h t IH].
  - inversion H1.
  - assert (length t = 0 \/ length t > 0)%nat as [H2 | H2] by lia.
    -- apply length_zero_iff_nil in H2. rewrite H2. simpl. destruct (Req_dec_T h h) as [H3 | H3]; lra.
    -- specialize (IH H2). rewrite MaxRlist_cons; auto. rewrite MaxRlist_index_cons; auto. destruct (Req_dec_T h (MaxRlist (h :: t))) as [H3 | H3].
       + simpl. rewrite MaxRlist_cons in H3; auto.
       + simpl. rewrite MaxRlist_cons in H3; auto. rewrite <- IH. pose proof (Rmax_neq_r h (MaxRlist t) H3) as H4. unfold Rmax.
         destruct (Rle_dec h (MaxRlist t)); lra.
Qed.

Definition build_list_for_lemma_2_22_a (l : list R) : list R :=
  let min := MinRlist l in
  let max := MaxRlist l in
  let mean := arithmetic_mean l in
  if (length l =? 0)%nat then [] else
  match (Req_dec_T min max) with 
  | left _ => l
  | right _ => mean :: (max + min - mean) :: remove_one (Req_dec_T) min (remove_one (Req_dec_T) max l)
  end.

Lemma list_eq {A : Type} : forall (h1 h2 : A) (t1 t2 : list A),
  h1 = h2 /\ t1 = t2 -> h1 :: t1 = h2 :: t2.
Proof.
  intros h1 h2 t1 t2 [Hh Ht].
  rewrite Hh, Ht.
  reflexivity.
Qed.

Ltac list_arith :=
  match goal with
  | |- ?l1 = ?l2 =>
    let rec compare l1 l2 :=
        match l1 with
        | [] => match l2 with
                | [] => reflexivity
                | _ => fail
                end
        | ?h1 :: ?t1 => match l2 with
                        | [] => fail 
                        | ?h2 :: ?t2 => apply list_eq; split; [try nra; try nia; auto | compare t1 t2]
                        end
        end in
    compare l1 l2
  | _ => fail 
  end.

Example ex_list_compare : forall a b, a = b -> [1;2;3;a] = [1;2;3;b].
Proof.
  intros a b H1.
  list_arith.
Qed.

Lemma sum_f_list_cons : forall h t, 
  sum_f 0 (length (h :: t) - 1) (fun i => nth i (h :: t) 0) = h + sum_f 0 (length t - 1) (fun i => nth i t 0).
Proof.
  intros h t. repeat rewrite sum_f_fold_right_equiv. replace (h :: t) with ([h] ++ t) by reflexivity.
  rewrite fold_right_app. simpl. lra.
Qed.

Lemma In_length_gt_1 : forall (l : list R) x1 x2,
  In x1 l -> In x2 l -> x1 <> x2 -> (length l > 1)%nat.
Proof.
  intros l x1 x2 H1 H2 H3. destruct l.
  - inversion H1.
  - destruct l.
    -- inversion H1 as [H4 | H4]; inversion H2 as [H5 | H5]; try lra; try inversion H4; try inversion H5.
    -- simpl. lia.
Qed.

Lemma build_list_for_lemma_2_22_a_length : forall l,
  length (build_list_for_lemma_2_22_a l) = length l.
Proof.
  intros l. unfold build_list_for_lemma_2_22_a. assert (length l = 0 \/ length l > 0)%nat as [H1 | H1] by lia.
  - apply length_zero_iff_nil in H1. rewrite H1. simpl. reflexivity.
  - assert (length l =? 0 = false)%nat as H3 by (apply Nat.eqb_neq; lia). rewrite H3. destruct (Req_dec_T (MinRlist l) (MaxRlist l)) as [H4 | H4]; auto.
    simpl. rewrite remove_one_In_length. 2 : { apply In_remove_one; auto. apply MinRlist_In. auto. }
    rewrite remove_one_In_length. 2 : { apply MaxRlist_In. auto. } assert (H5 : (length l > 1)%nat).
    { pose proof MaxRlist_In l H1 as H5. pose proof MinRlist_In l H1 as H6.  apply In_length_gt_1 with (x1 := MinRlist l) (x2 := MaxRlist l); auto. }
       lia.
Qed.

Lemma Max_Min_length1 : forall l,
  (length l = 1)%nat -> MaxRlist l = MinRlist l.
Proof.
  intros l H1. destruct l.
  - simpl in H1. lia.
  - simpl in H1. inversion H1 as [H2]. rewrite length_zero_iff_nil in H2. rewrite H2. simpl. reflexivity.
Qed.

Lemma Max_lengthl : forall l,
  (length l = 1)%nat -> l = [MaxRlist l].
Proof.
  intros l H1. destruct l.
  - simpl in H1. lia.
  - simpl in H1. inversion H1 as [H2]. rewrite length_zero_iff_nil in H2. rewrite H2. simpl. reflexivity.
Qed.

Lemma Max_Min_remove_one_length2 : forall l : list R,
  (length l = 2)%nat -> remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l) = [].
Proof.
  intros l H1. destruct l.
  - simpl in H1. lia.
  - destruct l.
    -- simpl in H1. lia.
    -- simpl in H1. inversion H1 as [H2]. rewrite length_zero_iff_nil in H2. rewrite H2. simpl. unfold Rmin. unfold Rmax. 
       destruct (Rle_dec r r0) as [H3 | H3]; destruct (Req_dec_T r r0) as [H4 | H4]; simpl; try lra.
       rewrite H4. destruct (Req_dec_T r0 r0); try lra. reflexivity. destruct (Req_dec_T r r); try lra. destruct (Req_dec_T r0 r0); try lra. reflexivity.
       destruct (Req_dec_T r r); try lra. simpl. destruct (Req_dec_T r0 r0); try lra. reflexivity.
Qed.

Lemma Min_Max_arith_mean_length2 : forall l : list R,
  (length l = 2)%nat -> arithmetic_mean l = (MaxRlist l + MinRlist l) / 2.
Proof.
  intros l H1. destruct l.
  - simpl in H1. lia.
  - destruct l.
    -- simpl in H1. lia.
    -- simpl in H1. inversion H1 as [H2]. rewrite length_zero_iff_nil in H2. rewrite H2. simpl. unfold arithmetic_mean. simpl. unfold Rmax, Rmin.
       destruct (Rle_dec r r0) as [H3 | H3]; destruct (Req_dec_T r r0) as [H4 | H4]; simpl; try lra.
Qed.

Lemma Min_Max_fold_right_Rmult_length_2 : forall l : list R,
  (length l = 2)%nat -> fold_right Rmult 1 l = (MaxRlist l) * (MinRlist l).
Proof.
  intros l H1. destruct l.
  - simpl in H1. lia.
  - destruct l.
    -- simpl in H1. lia.
    -- simpl in H1. inversion H1 as [H2]. rewrite length_zero_iff_nil in H2. rewrite H2. simpl. unfold Rmax, Rmin. destruct (Rle_dec r r0) as [H3 | H3]; simpl; lra.
Qed.

Lemma HdRel_trans : forall l x y,
  HdRel Rle y l -> x <= y -> HdRel Rle x l.
Proof.
  intros l x y H1 H2. induction l as [| h t IH].
  - apply HdRel_nil.
  - apply HdRel_cons. apply HdRel_inv in H1. lra.
Qed.

Lemma HdRel_app_one : forall l1 l2 x,
  HdRel Rle x (l1 ++ l2) -> HdRel Rle x l1.
Proof.
  intros l1 l2 x H1. destruct l1; auto. apply HdRel_cons. apply HdRel_inv in H1. lra.
Qed.

Lemma HdRel_app_two : forall l1 l2 x,
  (length l1 > 0)%nat -> HdRel Rle x l1 -> HdRel Rle x (l1 ++ l2).
Proof.
  intros l1 l2 x H1 H2. destruct l1.
  - simpl in H1. lia.
  - apply HdRel_cons. apply HdRel_inv in H2. lra.
Qed.

Lemma Sorted_cons_In : forall l x y,
  Sorted Rle (x :: l) -> In y l -> x <= y.
Proof.
  intros l x y H1 H2. induction l as [| h t IH].
  - inversion H2.
  - apply Sorted_inv in H1 as [H1 H3]. apply HdRel_inv in H3; auto. inversion H2 as [H4 | H4]; try lra. apply IH; auto.
    apply Sorted_cons; repeat apply Sorted_inv in H1 as [H5 H6]; auto. apply HdRel_trans with (y := h); auto.
Qed.

Lemma Sorted_Permutation_equal : forall l1 l2,
  Permutation l1 l2 -> Sorted Rle l1 -> Sorted Rle l2 -> l1 = l2.
Proof.
  intros l1 l2 H1 H2 H3. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2 H1 H3. apply Permutation_nil in H1. rewrite H1. reflexivity.
  - intros l2 H3 H4. destruct l2 as [| h2 t2].
    -- apply Permutation_sym in H3. apply Permutation_nil in H3. auto.
    -- apply Sorted_inv in H2 as [H2 H5]. specialize (IH H2 t2). assert (In h1 (h1 :: t1) -> In h1 (h2 :: t2)) as H6.
       { apply Permutation_in; auto. } assert (In h2 (h2 :: t2) -> In h2 (h1 :: t1)) as H7.
       { apply Permutation_in. apply Permutation_sym; auto. } assert (In h1 (h2 :: t2)) as H8 by (apply H6; left; reflexivity).
       assert (In h2 (h1 :: t1)) as H9 by (apply H7; left; reflexivity). assert (h1 = h2) as H10.
       {
        destruct H8 as [H8 | H8]; destruct H9 as [H9 | H9]; try lra; try inversion H8; try inversion H9. pose proof (Rtotal_order h1 h2) as [H10 | [H10 | H10]]; try lra.
        - assert (h2 <= h1) as H11. { apply Sorted_cons_In with (x := h2) (l := t2); auto. } lra.
        - assert (h1 <= h2) as H11. { apply Sorted_cons_In with (x := h1) (l := t1); auto. } lra.
       }
       
      rewrite H10. apply f_equal. apply IH.
      rewrite <- H10 in H3. apply Permutation_cons_inv in H3; auto. apply Sorted_inv in H4 as [H4 H11]; auto.
Qed.

Lemma count_occ_app_remove_eq : forall l1 l2 x,
  In x l1 -> count_occ Req_dec_T (remove_one Req_dec_T x l1) x = count_occ Req_dec_T l2 x -> count_occ Req_dec_T (l2 ++ [x]) x = count_occ Req_dec_T l1 x.
Proof.
  intros l1 l2 x H1 H2. simpl. rewrite count_occ_app. rewrite <- H2.
  pose proof (remove_one_In Req_dec_T x l1 H1) as H4. rewrite H4. assert (count_occ Req_dec_T l1 x > 0)%nat as H5 by (apply count_occ_In; auto).
  simpl. destruct (Req_dec_T x x); try lra; try lia.
Qed.

Lemma In_remove_one_In : forall l x y,
  In y (remove_one Req_dec_T x l) -> In y l.
Proof.
  intros l x y H1. induction l as [| h t IH].
  - inversion H1.
  - simpl in H1. destruct (Req_dec_T x h) as [H2 | H2].
    -- destruct (Req_dec_T h x) as [H3 | H3]; try lra. simpl. tauto.
    -- destruct (Req_dec_T h y) as [H3 | H3]; try lra. simpl. tauto. simpl. right. apply IH; auto.
       destruct (Req_dec_T h x); try lra. destruct H1 as [H1 | H1]; try lra. auto.
Qed.

Lemma In_remove_Max_le : forall l x,
  (length l > 0)%nat -> In x (remove_one Req_dec_T (MaxRlist l) l) -> x <= MaxRlist l.
Proof.
  intros l x H1 H2.
  assert (In (MaxRlist l) (remove_one Req_dec_T (MaxRlist l) l) \/ ~In (MaxRlist l) (remove_one Req_dec_T (MaxRlist l) l)) as [H3 | H3] by apply classic.
  - pose proof (MaxRlist_P1 l x) as H4. apply H4. apply In_remove_one_In with (x := MaxRlist l); auto.
  - apply In_remove_one_In in H2. apply MaxRlist_P1; auto.
Qed.

Lemma Sorted_app_one : forall l x,
  Sorted Rle l -> x >= MaxRlist l -> Sorted Rle (l ++ [x]).
Proof.
  intros l x H1 H2. induction l as [| h t IH].
  - simpl. apply Sorted_cons; auto.
  - simpl. assert (length t = 0 \/ length t > 0)%nat as [H3 | H3] by lia.
    -- apply length_zero_iff_nil in H3. rewrite H3. simpl. apply Sorted_cons; auto. apply HdRel_cons. rewrite H3 in H2. simpl in H2. lra.
    -- apply Sorted_inv in H1 as [H4 H5]. apply Sorted_cons; auto. apply IH; auto. rewrite MaxRlist_cons in H2; auto. unfold Rmax in H2. 
       destruct (Rle_dec h (MaxRlist t)); lra. apply HdRel_app_two with (l2 := [x]); auto.
Qed.

Lemma sum_remove_one_MaxList : forall l,
  (length l > 1)%nat -> sum_f 0 (length l - 1) (fun i => nth i l 0) = MaxRlist l + sum_f 0 (length l - 2) (fun i => nth i (remove_one Req_dec_T (MaxRlist l) l) 0).
Proof.
  intros l H1. assert (H2 : In (MaxRlist l) l) by (apply MaxRlist_In; lia). pose proof (exists_sorted_list_R l) as [l' [H3 H4]].
  rewrite sum_f_Permutation with (l1 := l) (l2 := l'); auto. assert (H5 : length l' = length l). { apply Permutation_length. apply Permutation_sym; auto. }
  replace (length l' - 1)%nat with (S (length l' - 2)) by lia. rewrite sum_f_i_Sn_f; try lia. replace (S (length l' - 2)) with (length l' - 1)%nat by lia.
  rewrite <- Sorted_MaxRlist; try lia; auto. rewrite Max_Permutation with (l1 := l) (l2 := l') at 1; auto. apply Rminus_eq_reg_r with (r := MaxRlist l').
  field_simplify. rewrite H5. pose proof (exists_sorted_list_R (remove_one Req_dec_T (MaxRlist l) l)) as [l'' [H6 H7]].
  replace (length l - 2)%nat with (length (remove_one Req_dec_T (MaxRlist l) l) - 1)%nat at 2. 2 : { rewrite remove_one_In_length; try lia. apply MaxRlist_In; lia. }
  rewrite sum_f_Permutation with (l1 := remove_one Req_dec_T (MaxRlist l) l) (l2 := l''); auto. assert (length (remove_one Req_dec_T (MaxRlist l) l) = length l'')%nat as H8.
  { apply Permutation_length; auto. } replace (length l'' - 1)%nat with (length l - 2)%nat. 2 : { rewrite <- H8. rewrite remove_one_In_length; try lia. apply MaxRlist_In; lia. }
  replace (sum_f 0 (length l - 2) (fun i : nat => nth i l'' 0)) with (sum_f 0 (length l - 2) (fun i : nat => nth i (l'' ++ [MaxRlist l]) 0)).
  2 : { apply sum_f_equiv; try lia. intros i H9. rewrite app_nth1. reflexivity. rewrite <- H8. rewrite remove_one_In_length; try lia. apply MaxRlist_In; lia. }
  apply sum_f_equiv; try lia. intros i H9. assert (H10 : l'' ++ [MaxRlist l] = l').
  - assert (forall x, In x l'' -> In x (remove_one Req_dec_T (MaxRlist l) l)) as H10. { intros x H10. apply Permutation_in with (l := l''); auto. apply Permutation_sym; auto. }
    apply Sorted_Permutation_equal; auto. apply Permutation_trans with (l' := l); auto. rewrite (Permutation_count_occ Req_dec_T). intros x. specialize (H10 x).
    assert (x = MaxRlist l \/ x <> MaxRlist l) as [H11 | H11] by lra. rewrite H11. apply count_occ_app_remove_eq with (l1 := l); auto.
    rewrite (Permutation_count_occ Req_dec_T) in H7. specialize (H7 (MaxRlist l)). auto. rewrite (Permutation_count_occ Req_dec_T) in H7.
    specialize (H7 x). rewrite count_occ_remove_one_neq in H7; auto. rewrite count_occ_app. rewrite H7. simpl. destruct (Req_dec_T (MaxRlist l) x); try lra; try lia.
    pose proof (MaxRlist_In l'') as H11. specialize (H10 (MaxRlist l'')). assert (length l'' > 0)%nat as H12. { rewrite <- H8. rewrite remove_one_In_length; auto. lia. }
    specialize (H10 (H11 H12)). assert (H13 : MaxRlist l >= MaxRlist l''). { apply Rle_ge. apply In_remove_Max_le; auto; lia. }
    apply Sorted_app_one; auto.
  - rewrite H10. reflexivity.
Qed.

Lemma Permutation_MaxRlist : forall l1 l2,
  Permutation l1 l2 -> MaxRlist l1 = MaxRlist l2.
Proof.
  intros l1 l2 H1. assert (length l1 = 0 \/ length l1 > 0)%nat as [H2 | H2] by lia.
  - apply length_zero_iff_nil in H2. rewrite H2 in *. apply Permutation_nil in H1. rewrite H1. reflexivity.
  - pose proof (Permutation_length H1) as H3. assert (forall x, In x l1 -> In x l2) as H4. { intro x. apply Permutation_in; auto. }
    assert (forall x, In x l2 -> In x l1) as H5. { intro x. apply Permutation_in. apply Permutation_sym; auto. }
    pose proof (MaxRlist_In l1) as H6. pose proof (MaxRlist_In l2) as H7. pose proof (MaxRlist_P1 l1) as H8. pose proof (MaxRlist_P1 l2) as H9.
    assert (H10 : In (MaxRlist l1) l2). { apply H4. auto. } assert (H11 : In (MaxRlist l2) l1). { apply H5. apply H7. rewrite <- H3; auto. }
    specialize (H8 (MaxRlist l2) H11). specialize (H9 (MaxRlist l1) H10). lra.
Qed.

Lemma Permutation_MinRlist : forall l1 l2,
  Permutation l1 l2 -> MinRlist l1 = MinRlist l2.
Proof.
  intros l1 l2 H1. assert (length l1 = 0 \/ length l1 > 0)%nat as [H2 | H2] by lia.
  - apply length_zero_iff_nil in H2. rewrite H2 in *. apply Permutation_nil in H1. rewrite H1. reflexivity.
  - pose proof (Permutation_length H1) as H3. assert (forall x, In x l1 -> In x l2) as H4. { intro x. apply Permutation_in; auto. }
    assert (forall x, In x l2 -> In x l1) as H5. { intro x. apply Permutation_in. apply Permutation_sym; auto. }
    pose proof (MinRlist_In l1) as H6. pose proof (MinRlist_In l2) as H7. pose proof (MinRlist_P1 l1) as H8. pose proof (MinRlist_P1 l2) as H9.
    assert (H10 : In (MinRlist l1) l2). { apply H4. auto. } assert (H11 : In (MinRlist l2) l1). { apply H5. apply H7. rewrite <- H3; auto. }
    specialize (H8 (MinRlist l2) H11). specialize (H9 (MinRlist l1) H10). lra.
Qed.

Lemma Sorted_Permutation_min_cons : forall l1 l2 r,
  Sorted Rle (r :: l1) -> Permutation l2 (r :: l1) -> MinRlist l2 = r.
Proof.
  intros l1 l2 r H1 H2. assert (length l2 = 0 \/ length l2 > 0)%nat as [H3 | H3] by lia.
  - apply length_zero_iff_nil in H3. rewrite H3 in *. apply Permutation_nil in H2. inversion H2.
  - pose proof (Permutation_length H2) as H4. assert (forall x, In x l2 -> In x (r :: l1)) as H5. { intros x H6. apply Permutation_in with (l := l2); auto. }
    pose proof (MinRlist_In l2) as H6. pose proof (MinRlist_P1 l2) as H7. assert (H8 : In (MinRlist l2) (r :: l1)). { apply H5. auto. }
    apply Sorted_MinRlist in H1; (simpl; try lia). apply Permutation_MinRlist in H2. rewrite H2. rewrite H1. reflexivity.
Qed.

Lemma Permutation_remove_one : forall l1 l2 l3 r,
  Permutation l1 (r :: l2) -> Permutation (remove_one Req_dec_T r l1) l3 -> Permutation l2 l3.
Proof.
  intros l1 l2 l3 r H1 H2. assert (length l1 = 0 \/ length l1 > 0)%nat as [H3 | H3] by lia.
  - apply length_zero_iff_nil in H3. rewrite H3 in *. apply Permutation_nil in H1. inversion H1.
  - rewrite (Permutation_count_occ Req_dec_T). intros x. rewrite (Permutation_count_occ Req_dec_T) in H1, H2. specialize (H1 x). specialize (H2 x).
    rewrite <- H2. assert (x = r \/ x <> r) as [H4 | H4] by lra.
    -- rewrite H4 in *. simpl in H1. destruct (Req_dec_T r r) as [H5 | H5]; try lra. assert (In r l1 \/ ~In r l1) as [H6 | H6] by apply classic.
       ++ rewrite remove_one_In; auto. rewrite H1. simpl. auto.
       ++ rewrite (count_occ_not_In Req_dec_T) in H6. lia.
    -- simpl in H1. destruct (Req_dec_T r x) as [H5 | H5]; try lra; clear H5. rewrite <- H1. rewrite count_occ_remove_one_neq; auto.
Qed.

Lemma sum_remove_one_MinList : forall l,
  (length l > 1)%nat -> sum_f 0 (length l - 1) (fun i => nth i l 0) = MinRlist l + sum_f 0 (length l - 2) (fun i => nth i (remove_one Req_dec_T (MinRlist l) l) 0).
Proof.
  intros l H1. assert (H2 : In (MinRlist l) l) by (apply MinRlist_In; lia). pose proof (exists_sorted_list_R l) as [l' [H3 H4]].
  rewrite sum_f_Permutation with (l1 := l) (l2 := l'); auto. assert (H5 : length l' = length l). { apply Permutation_length. apply Permutation_sym; auto. }
  rewrite sum_f_Si; try lia. rewrite <- Sorted_MinRlist; try lia; auto.  try lia; auto. rewrite Min_Permutation with (l1 := l) (l2 := l') at 1; auto.
  apply Rminus_eq_reg_r with (r := MinRlist l'). field_simplify. rewrite H5. destruct l'.
  - simpl in H5. lia. 
  - replace (length l - 1)%nat with (length l'). 2 : { simpl in H5. lia. } rewrite sum_f_nth_cons_0. 2 : { simpl in H5; lia. }
    pose proof (exists_sorted_list_R (remove_one Req_dec_T (MinRlist l) l)) as [l'' [H6 H7]]. replace (length l - 2)%nat with (length l'' - 1)%nat.
    2 : { rewrite <- H7. rewrite remove_one_In_length; try lia. apply MinRlist_In; lia. }
    replace (length l'')%nat with (length (remove_one Req_dec_T (MinRlist l) l)) by (apply Permutation_length; auto).
    rewrite sum_f_Permutation with (l1 := remove_one Req_dec_T (MinRlist l) l) (l2 := l''); auto.
    replace (length l')%nat with (length l'').
    2 : { simpl in H5. replace (length l') with (length l - 1)%nat by lia. apply Permutation_length in H7; auto. rewrite remove_one_In_length in H7. lia. apply MinRlist_In; lia. }
    apply sum_f_equiv; try lia. intros i H8. replace l'' with l'; auto. apply Sorted_Permutation_equal; auto. 2 : { apply Sorted_inv in H3; tauto. }
    rewrite (Permutation_count_occ Req_dec_T). intros x. pose proof H7 as H9. rewrite (Permutation_count_occ Req_dec_T) in H7. specialize (H7 x).
    rewrite <- H7. assert (MinRlist l = r) as H10. { apply Sorted_Permutation_min_cons with (l1 := l') (l2 := l); auto. } rewrite H7. apply Permutation_count_occ; auto.
    apply Permutation_remove_one with (l1 := l) (r := r); auto. rewrite H10 in H9. auto. 
Qed.

Lemma MinRlist_eq_MaxRlist_repeat : forall l,
  (length l > 1)%nat -> MinRlist l = MaxRlist l -> l = repeat (MinRlist l) (length l).
Proof.
  intros l H1 H2. apply MinRlist_eq_MaxRlist in H2; try lia. assert (H3 : Forall (eq (nth 0 l 0)) l).
  { apply Forall_forall. intros x H3. rewrite Forall_forall in H2. specialize (H2 x). rewrite H2; auto. }
   apply Forall_eq_repeat; auto. replace (MinRlist l) with (nth 0 l 0); auto.
   rewrite Forall_forall in H3. apply H3. apply MinRlist_In; lia.
Qed.

Lemma remove_one_In_repeat : forall x n l,
  l = repeat x n -> In x l -> remove_one Req_dec_T x (repeat x (length l)) = repeat x (length l - 1).
Proof.
  intros x n l H1 H2. assert (H3 : count_occ Req_dec_T (repeat x (length l)) x = n).
  { rewrite List.count_occ_repeat_eq; try lra. rewrite <- (repeat_length x n). rewrite H1. reflexivity. }
  destruct l. inversion H2. apply eq_sym, repeat_eq_cons in H1 as [H4 H5]. rewrite H4. simpl. destruct (Req_dec_T r r) as [H6 | H6]; try lra; clear H6.
  rewrite Nat.sub_0_r. reflexivity.
Qed.

Lemma repeat_Succ : forall (x : R) n,
  repeat x (S n) = x :: repeat x n.
Proof.
  intros x n. simpl. reflexivity.
Qed.

Lemma MinRlist_repeat : forall x n,
  (n > 0)%nat -> MinRlist (repeat x n) = x.
Proof.
  intros x n H1. induction n as [| n' IH].
  - inversion H1.
  - assert (n' = 0 \/ n' > 0)%nat as [H2 | H2] by lia.
    -- rewrite H2. simpl. reflexivity.
    -- specialize (IH H2). rewrite repeat_Succ. rewrite MinRlist_cons. rewrite IH. unfold Rmin. destruct (Rle_dec x x); lra. rewrite repeat_length; lia.
Qed.

Lemma Min_l_eq_Min_remove_one_Max : forall l,
  (length l > 1)%nat -> MinRlist l = MinRlist (remove_one Req_dec_T (MaxRlist l) l).
Proof.
  intros l H1. assert (In (MaxRlist l) l) as H2 by (apply MaxRlist_In; lia). assert (In (MinRlist l) l) as H3 by (apply MinRlist_In; lia).
  assert (MinRlist l = MaxRlist l \/ MinRlist l <> MaxRlist l) as [H4 | H4] by apply classic.
  - pose proof (MinRlist_eq_MaxRlist_repeat l H1 H4) as H5. rewrite H5 at 3. rewrite H4. rewrite remove_one_In_repeat with (n := length l); auto.
    2 : rewrite <- H4; auto. rewrite MinRlist_repeat; auto; lia.
  - assert (H5 : In (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l)). { apply In_remove_one; auto. } pose proof In_remove_one_In as H6.
    pose proof (Rtotal_order (MinRlist l) (MinRlist (remove_one Req_dec_T (MaxRlist l) l))) as [H7 | [H7 | H7]]; try lra.
    -- assert (H8 : MinRlist (remove_one Req_dec_T (MaxRlist l) l) <= MinRlist l). { apply MinRlist_P1; auto. } lra.
    -- pose proof (MinRlist_In (remove_one Req_dec_T (MaxRlist l) l)) as H8. assert (H9 : In (MinRlist (remove_one Req_dec_T (MaxRlist l) l)) l). 
       { apply H6 with (x := MaxRlist l). apply H8. rewrite remove_one_In_length; auto. lia. } 
       assert (H10 : MinRlist l <= MinRlist (remove_one Req_dec_T (MaxRlist l) l)). { apply MinRlist_P1; auto. } lra.
Qed.

Lemma geometric_mean_cons : forall h t,
  pos_list (h :: t) -> geometric_mean (h :: t) = Rpower (h * (geometric_mean t) ^ (length t)) (1 / INR (S (length t))).
Proof.
  intros h t H1. apply pos_list_cons in H1 as [H1 H2]. unfold geometric_mean. destruct (Nat.eq_dec (length (h :: t))) as [H3 | H3]; simpl in H3; try lia.
  replace (fold_right Rmult 1 (h :: t)) with (h * fold_right Rmult 1 t) by reflexivity. replace (INR (length (h :: t))) with (INR (S (length t))) by reflexivity.
  clear H3. assert (length t = 0 \/ length t > 0)%nat as [H3 | H3] by lia.
  - rewrite H3. apply length_zero_iff_nil in H3. rewrite H3. simpl. replace (1 / 1) with 1 by lra. reflexivity.
  - destruct (Nat.eq_dec (length t)) as [H4 | H4]; try lia. assert (H5 : 0 < fold_right Rmult 1 t). { apply fold_right_mult_pos_list_gt_0; auto. }
    assert (H6 : Rpower (fold_right Rmult 1 t) (1 / INR (length t)) ^ length t > 0). { rewrite <- Rpower_pow; repeat apply Rpower_gt_0; auto. }
    assert (H7 : 0 < Rpower (fold_right Rmult 1 t) (1 / INR (length t))). { apply Rpower_gt_0; auto. }
    assert (H8 : 0 < Rpower (h * fold_right Rmult 1 t) (1 / INR (S (length t)))). { apply Rpower_gt_0; nra. }
    assert (H9 : 0 < Rpower (h * Rpower (Rpower (fold_right Rmult 1 t) (1 / INR (length t))) (INR (length t))) (INR (S (length t)))). 
    { apply Rpower_gt_0; try nra. rewrite Rpower_pow; auto. nra. }
    assert (H10 : 0 < Rpower (h * Rpower (fold_right Rmult 1 t) (1 / INR (length t)) ^ length t) (INR (S (length t)))).
    { apply Rpower_gt_0; try nra. }
    apply pow_eq_1 with (n := length t); auto; try apply Rpower_gt_0; try nra. 
    assert (Rpower (h * fold_right Rmult 1 t) (1 / INR (S (length t))) ^ length t = (Rpower (h * fold_right Rmult 1 t) (INR (length t) / INR (S (length t))))) as H11.
    { rewrite <- Rpower_pow; auto. rewrite Rpower_mult. replace (1 / INR (S (length t)) * INR (length t)) with (INR (length t) / INR (S (length t))) by nra. nra. }
    repeat rewrite <- Rpower_pow; repeat rewrite Rpower_mult; auto.
    2 : 
    { 
      repeat apply Rpower_gt_0. apply Rmult_gt_reg_r with (r := 1 / h). unfold Rdiv. rewrite Rmult_1_l. 
      apply Rinv_pos; auto. field_simplify; try nra. unfold Rdiv. rewrite Rmult_0_l. apply Rpower_gt_0. auto. 
    } 
    replace ((1 / INR (S (length t)) * INR (length t))) with ((INR (length t) / INR (S (length t)))) by nra.
    replace (1 / INR (length t) * INR (length t)) with 1. 2 : { field; apply not_0_INR; auto. }
    rewrite Rpower_1; auto.
Qed.

Lemma arithmetic_mean_nil : arithmetic_mean [] = 0.
Proof.
  compute. lra.
Qed.

Lemma geometric_mean_nil : geometric_mean [] = 0.
Proof.
  unfold geometric_mean. simpl. nra.
Qed.

Lemma arithmetic_mean_cons : forall h t,
  arithmetic_mean (h :: t) = (h + arithmetic_mean t * INR (length t)) / INR (S (length t)).
Proof.
  intros h t. unfold arithmetic_mean. replace (fold_right Rplus 0 (h :: t)) with (h + fold_right Rplus 0 t) by reflexivity. 
  replace (INR (length (h :: t))) with (INR (S (length t))) by reflexivity. assert (length t = 0 \/ length t > 0)%nat as [H1 | H1] by lia.
  - rewrite H1. apply length_zero_iff_nil in H1. rewrite H1. simpl. lra.
  - field; split; apply not_0_INR; lia. 
Qed.

Lemma arithmetic_mean_cons_l : forall l,
  arithmetic_mean (arithmetic_mean l :: l) = arithmetic_mean l.
Proof.
  intros l. assert (length l = 0 \/ length l > 0)%nat as [H1 | H1] by lia.
  - apply length_zero_iff_nil in H1 as H2. rewrite H2. compute. lra.
  - rewrite arithmetic_mean_cons. apply Rmult_eq_reg_r with (r := INR (S (length l))).
    2 : { apply not_0_INR. lia. } field_simplify. 2 : { apply not_0_INR; lia. }
    rewrite S_INR. nra.
Qed.

Lemma arithmetic_mean_pos_list : forall l,
  pos_list l -> (length l > 0)%nat -> arithmetic_mean l > 0.
Proof.
  intros l H1. unfold pos_list in H1. rewrite Forall_forall in H1. induction l as [| h t IH].
  - simpl; lia.
  - intro H2. rewrite arithmetic_mean_cons. assert (length t = 0 \/ length t > 0)%nat as [H3 | H3] by lia.
    -- rewrite H3. apply length_zero_iff_nil in H3. rewrite H3. rewrite arithmetic_mean_nil. simpl. field_simplify. apply H1. left; reflexivity.
    -- assert (H4 : arithmetic_mean t > 0). { apply IH; auto. intros x H4. apply H1. right; auto. }
       assert (H5 : INR (length t) > 0). { apply lt_0_INR. lia. } assert (H6 : INR (S (length t)) > 0). { rewrite S_INR. lra. }
       apply Rmult_gt_reg_r with (r := INR (S (length t))); auto. field_simplify; try lra. specialize (H1 h (or_introl eq_refl)). nra.
Qed.

Lemma arithmetic_mean_build_list_2_22_a_equiv : forall l,
  arithmetic_mean (build_list_for_lemma_2_22_a l) = arithmetic_mean l.
Proof.
  intros l. unfold build_list_for_lemma_2_22_a. assert (length l = 0 \/ length l = 1 \/ length l = 2 \/ length l > 2)%nat as [H1 | [H1 | [H1 | H1]]] by lia.
  - rewrite H1. simpl. apply length_zero_iff_nil in H1. rewrite H1. reflexivity.
  - rewrite H1. simpl. apply Max_lengthl in H1. destruct (Req_dec_T (MinRlist l) (MaxRlist l)) as [H2 | H2]; auto. 
    rewrite H1 in H2. simpl in H2. tauto.
  - rewrite H1. simpl. destruct (Req_dec_T (MinRlist l) (MaxRlist l)) as [H2 | H2]; auto. replace (remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l))
    with ([] : list R). 2 : { rewrite Max_Min_remove_one_length2; auto. } rewrite arith_mean_equiv. unfold arithmetic_mean_prime. simpl. apply Rmult_eq_reg_r with (r := INR 2).
    2 : { simpl. lra. } rewrite sum_f_i_Sn_f; try lia. rewrite sum_f_0_0. field_simplify. rewrite Min_Max_arith_mean_length2; auto. lra. 
  - assert (length l =? 0 = false)%nat as H2 by (apply Nat.eqb_neq; lia). rewrite H2.
    destruct (Req_dec_T (MinRlist l) (MaxRlist l)) as [H3 | H3]; auto.
    rewrite arith_mean_equiv. rewrite arith_mean_equiv at 3. unfold arithmetic_mean_prime. 
    apply Rmult_eq_reg_r with (r := INR (length l)). 2 : { apply not_0_INR; lia. } field_simplify. 2 : { apply not_0_INR; lia. }
    replace (arithmetic_mean l :: MaxRlist l + MinRlist l - arithmetic_mean l :: remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l)) with (build_list_for_lemma_2_22_a l).
    2 : { unfold build_list_for_lemma_2_22_a. rewrite H2. destruct (Req_dec_T (MinRlist l) (MaxRlist l)); try lra. reflexivity. }
    2 : { apply not_0_INR. simpl. lia. } replace (length (build_list_for_lemma_2_22_a l)) with (length l). 2 : { rewrite build_list_for_lemma_2_22_a_length; auto. }
    field_simplify. 2 : { apply not_0_INR. simpl. lia. }
    rewrite sum_remove_one_MaxList; try lia. replace (length l - 2)%nat with (length (remove_one Req_dec_T (MaxRlist l) l) - 1)%nat by (rewrite remove_one_In_length; try lia; apply MaxRlist_In; lia).
    rewrite sum_remove_one_MinList. rewrite <- Min_l_eq_Min_remove_one_Max. 2 : { apply In_length_gt_1 with (x1 := MinRlist l) (x2 := MaxRlist l); auto. apply MinRlist_In; lia. apply MaxRlist_In; lia. }
    2 : { rewrite remove_one_In_length; try lia. apply MaxRlist_In; lia. } replace (length (remove_one Req_dec_T (MaxRlist l) l) - 2)%nat with (length l - 3)%nat.
    2 : { rewrite remove_one_In_length; try lia. apply MaxRlist_In; lia. } 
    rewrite sum_f_Si; try lia. rewrite sum_f_Si; try lia. replace (nth 1 (build_list_for_lemma_2_22_a l) 0) with (MaxRlist l + MinRlist l - arithmetic_mean l).
    2 : { unfold build_list_for_lemma_2_22_a. rewrite H2. destruct (Req_dec_T (MinRlist l) (MaxRlist l)); try lra. reflexivity. }
    replace (nth 0 (build_list_for_lemma_2_22_a l) 0) with (arithmetic_mean l).
    2 : { unfold build_list_for_lemma_2_22_a. rewrite H2. destruct (Req_dec_T (MinRlist l) (MaxRlist l)); try lra. reflexivity. }
    apply Rminus_eq_reg_r with (r := MinRlist l + MaxRlist l). field_simplify. rewrite sum_f_reindex with (s := 2%nat); try lia. unfold build_list_for_lemma_2_22_a. rewrite H2.
    destruct (Req_dec_T (MinRlist l) (MaxRlist l)); try lra. clear n.
    replace (sum_f (2 - 2) (length l - 1 - 2) (fun x : nat => nth (x + 2) (arithmetic_mean l :: MaxRlist l + MinRlist l - arithmetic_mean l :: remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l)) 0)) with
    (sum_f 0 (length l - 3) (fun x : nat => nth x (remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l)) 0)).
    2 : { replace (2 - 2)%nat with 0%nat by lia. replace (length l - 1 - 2)%nat with (length l - 3)%nat by lia. apply sum_f_equiv; try lia. intros k H8. 
          replace (arithmetic_mean l :: MaxRlist l + MinRlist l - arithmetic_mean l :: remove_one Req_dec_T (MinRlist l)
   (remove_one Req_dec_T (MaxRlist l) l)) with ([arithmetic_mean l] ++ [MaxRlist l + MinRlist l - arithmetic_mean l] ++ remove_one Req_dec_T (MinRlist l)
   (remove_one Req_dec_T (MaxRlist l) l)) by reflexivity. repeat rewrite app_nth2; try (simpl; lia). simpl. replace (k + 2 - 1 - 1)%nat with k by lia. reflexivity. } reflexivity.
Qed.

Lemma MinRlist_neq_MaxRlist : forall l,
  (length l > 0)%nat -> MinRlist l <> MaxRlist l <-> ~Forall (eq (MinRlist l)) l.
Proof.
  intros l H1. split.
  - intro H2. intro H3. assert (H4 : MinRlist l = MaxRlist l). { rewrite Forall_forall in H3. assert (length l > 0)%nat as H4 by lia.
    specialize (H3 (MaxRlist l) (MaxRlist_In l H4)). auto. } lra.
  - intro H2. intro H3. apply H2. apply Forall_forall. intros x H4. apply MinRlist_eq_MaxRlist in H3; auto.
    assert (0 < length l)%nat as H5 by lia. apply Forall_eq_imp_eq_nth in H5. rewrite H5 in H3. specialize (H3 (MinRlist l)).
    specialize (H3 (MinRlist_In l H1)). tauto.
Qed.

Lemma MaxRlist_gt_arith_mean : forall l,
  (length l > 0)%nat -> MinRlist l <> MaxRlist l -> MaxRlist l > arithmetic_mean l.
Proof.
  intros l H1 H2. pose proof MinElementLessThanMean as H3. pose proof MaxElementGreaterThanMean as H4.
  pose proof (exists_sorted_list_R l) as [l' [H5 H6]]. apply Permutation_length in H6 as H7. assert (length l' > 0)%nat as H8 by lia.
  pose proof (Sorted_MaxRlist l' H5 H8) as H9. assert (MaxRlist l' = MaxRlist l) as H10. { apply Permutation_MaxRlist; auto. apply Permutation_sym; auto. }
  rewrite <- H10. rewrite arith_mean_Permtation_eq with (l1 := l) (l2 := l'); auto. rewrite Sorted_MaxRlist; auto. apply H4; auto. 
  intro H11. replace ((fun x : R => x = nth 0 l' 0)) with (eq (MinRlist l')) in H11.
  2 : { apply functional_extensionality. intros x. rewrite <- Sorted_MinRlist; auto. rewrite <- Permutation_MinRlist with (l1 := l) (l2 := l'); auto.
        apply propositional_extensionality. split; intros; auto. }
  apply MinRlist_neq_MaxRlist with (l := l'); auto. assert (MinRlist l' = MinRlist l) as H12. { apply Permutation_MinRlist; auto. apply Permutation_sym; auto. }
  assert (H13 : MinRlist l' = nth 0 l' 0). { rewrite <- Sorted_MinRlist; auto. } pose proof (MaxRlist_In l' H8) as H14. rewrite Forall_forall in H11.
  specialize (H11 (MaxRlist l') H14). nra.  pose proof (MaxRlist_In l' H8) as H15. rewrite Forall_forall in H11. specialize (H11 (MaxRlist l') H15). nra.
Qed.

Lemma MinRlist_eq_MaxRlist_eq_arith_mean : forall l,
  (length l > 0)%nat -> MinRlist l = MaxRlist l -> MinRlist l = arithmetic_mean l.
Proof.
  intros l H1 H2. apply MinRlist_eq_MaxRlist in H2; auto. apply arithmetic_mean_all_equal in H2 as H3; auto.
  rewrite H3. pose proof (MinRlist_In l H1) as H4. rewrite Forall_forall in H2. specialize (H2 (MinRlist l) H4). auto.
Qed.

Lemma Min_Max_plus_gt_arith_mean : forall l,
  pos_list l -> MinRlist l + MaxRlist l > arithmetic_mean l.
Proof.
  intros l H1. assert (length l = 0 \/ length l > 0)%nat as [H2 | H2] by lia.
  - apply length_zero_iff_nil in H2. rewrite H2. compute; lra.
  - assert (MinRlist l = MaxRlist l \/ MinRlist l <> MaxRlist l) as [H3 | H3] by apply classic.
    -- rewrite H3. apply MinRlist_eq_MaxRlist_eq_arith_mean in H3 as H4; try lia. rewrite <- H3.
       unfold pos_list in H1. rewrite Forall_forall in H1. specialize (H1 (MaxRlist l) (MaxRlist_In l H2)). lra.
    -- pose proof (MaxRlist_gt_arith_mean l H2 H3) as H4. unfold pos_list in H1. rewrite Forall_forall in H1. specialize (H1 (MinRlist l) (MinRlist_In l H2)).
       lra.
Qed.

Lemma MinRlist_lt_arith_mean : forall l,
  (length l > 0)%nat -> MinRlist l <> MaxRlist l -> MinRlist l < arithmetic_mean l.
Proof.
  intros l H1 H2. pose proof MinElementLessThanMean as H3. pose proof MaxElementGreaterThanMean as H4.
  pose proof (exists_sorted_list_R l) as [l' [H5 H6]]. apply Permutation_length in H6 as H7. assert (length l' > 0)%nat as H8 by lia.
  pose proof (Sorted_MinRlist l' H5 H8) as H9. assert (MinRlist l' = MinRlist l) as H10. { apply Permutation_MinRlist; auto. apply Permutation_sym; auto. }
  rewrite <- H10. rewrite arith_mean_Permtation_eq with (l1 := l) (l2 := l'); auto. rewrite Sorted_MinRlist; auto. apply H3; auto. 
  intro H11. replace ((fun x : R => x = nth 0 l' 0)) with (eq (MinRlist l')) in H11.
  2 : { apply functional_extensionality. intros x. rewrite <- Sorted_MinRlist; auto. rewrite <- Permutation_MinRlist with (l1 := l) (l2 := l'); auto.
        apply propositional_extensionality. split; intros; auto. }
  apply MinRlist_neq_MaxRlist with (l := l'); auto. assert (MaxRlist l' = MaxRlist l) as H12. { apply Permutation_MaxRlist; auto. apply Permutation_sym; auto. }
  assert (H13 : MaxRlist l' = MinRlist l'). { rewrite Forall_forall in H11. specialize (H11 (MaxRlist l')). rewrite H11. reflexivity. apply MaxRlist_In; lia. }
  nra. pose proof (MaxRlist_In l' H8) as H14. rewrite Forall_forall in H11. specialize (H11 (MaxRlist l') H14). nra.
Qed.

Lemma pos_list_remove_one : forall l x,
  pos_list l -> pos_list (remove_one Req_dec_T x l).
Proof.
  intros l x H1. unfold pos_list in H1. rewrite Forall_forall in H1. unfold pos_list. rewrite Forall_forall. intros y H2.
  apply In_remove_one_In in H2. apply H1; auto.
Qed.

Lemma Rpower_0 : forall x, Rpower 0 x = 1.
Proof.
  intro x. unfold Rpower. unfold ln. destruct (Rlt_dec 0 0) as [H1 | H1].
  - assert (0 < 0 -> False) as H2 by nra. exfalso. apply H2; auto.
  - rewrite Rmult_0_r. rewrite exp_0. reflexivity.
Qed.

Lemma fold_right_Rmult_remove_one_In : forall l x,
  (length l > 0)%nat -> pos_list l -> In x l -> fold_right Rmult 1 (remove_one Req_dec_T x l) = fold_right Rmult 1 l / x.
Proof.
  intros l x H1 H2 H3. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct (Req_dec_T x h) as [H4 | H4].
    -- assert (length t = 0 \/ length t > 0)%nat as [H5 | H5] by lia.
       + apply length_zero_iff_nil in H5. rewrite H5. simpl. destruct (Req_dec_T h x) as [H6 | H6]; try lra. rewrite H6. simpl. field. 
          unfold pos_list in H2. rewrite Forall_forall in H2. specialize (H2 x H3). lra.
       + apply pos_list_cons in H2 as [H2 H6]. destruct (Req_dec_T h x) as [H7 | H7]; try lra. rewrite H7. simpl. field. lra.
    -- assert (length t = 0 \/ length t > 0)%nat as [H5 | H5] by lia. 
       + apply length_zero_iff_nil in H5. rewrite H5 in H3. simpl in H3. lra.
       + destruct (Req_dec_T h x) as [H6 | H6]; try lra; clear H6. simpl. rewrite IH; auto; try lra. apply pos_list_cons in H2 as [H2 H6]; auto.
         destruct H3 as [H3 | H3]; auto; try lra.
Qed.

Lemma geometric_mean_build_list_2_22_a_lt : forall l,
  pos_list l -> geometric_mean (build_list_for_lemma_2_22_a l) >= geometric_mean l.
Proof.
  intros l H1. unfold build_list_for_lemma_2_22_a. assert (length l = 0 \/ length l = 1 \/ length l = 2 \/ length l > 2)%nat as [H2 | [H2 | [H2 | H2]]] by lia.
  - rewrite H2. simpl. apply length_zero_iff_nil in H2. rewrite H2. simpl. lra.
  - rewrite H2. simpl. destruct (Req_dec_T (MinRlist l) (MaxRlist l)) as [H3 | H3]; try lra. pose proof (Max_Min_length1 l H2) as H4; lra.
  - rewrite H2. simpl. destruct (Req_dec_T (MinRlist l) (MaxRlist l)) as [H3 | H3]; try lra. replace (remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l))
    with ([] : list R). 2 : { rewrite Max_Min_remove_one_length2; auto. } unfold geometric_mean. simpl. apply Rle_ge.
    replace (INR 2) with (INR (length l)). 2 : { rewrite H2. reflexivity. } rewrite H2. simpl. rewrite Min_Max_arith_mean_length2; auto.
    rewrite Rmult_1_r. rewrite Rdiv_plus_distr. replace (MaxRlist l + MinRlist l - (MaxRlist l / 2 + MinRlist l / 2)) with (MaxRlist l / 2 + MinRlist l / 2) by lra.
    rewrite r_mult_r_is_Rsqr. replace (1 / (1 + 1)) with (/ 2) by lra. assert (H4: 0 < fold_right Rmult 1 l) by (apply fold_right_mult_pos_list_gt_0; auto).
    assert (H5 : 0 < (MaxRlist l / 2 + MinRlist l / 2)).
    {
      unfold pos_list in H1. rewrite Forall_forall in H1. assert (length l > 0)%nat as H5 by lia.
      specialize (H1 (MinRlist l) (MinRlist_In l H5)) as H6. specialize (H1 (MaxRlist l) (MaxRlist_In l H5)) as H7. lra. 
    }
    assert (0 < (MaxRlist l / 2 + MinRlist l / 2)^2) as H6 by (apply pow2_gt_0; lra).
    rewrite Rsqr_pow2. repeat rewrite Rpower_sqrt; auto. apply sqrt_le_1; try lra. rewrite Min_Max_fold_right_Rmult_length_2; auto; nra.
  - assert (length l =? 0 = false)%nat as H3 by (apply Nat.eqb_neq; lia). rewrite H3.
    destruct (Req_dec_T (MinRlist l) (MaxRlist l)) as [H4 | H4]; try lra.
    unfold geometric_mean. destruct (Nat.eq_dec (length l) 0) as [H5 | H5]; try lia.
    repeat rewrite list_len_cons.
    destruct (Nat.eq_dec (S (S (length (remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l))))) 0) as [H6 | H6]; try lia; clear H6.
    repeat rewrite remove_one_In_length; try lia. 2 : { apply MaxRlist_In; lia. } 2 : { rewrite Min_l_eq_Min_remove_one_Max; try lia. apply MinRlist_In. rewrite remove_one_In_length; try lia. apply MaxRlist_In; lia. }
    replace (S (S (Init.Nat.pred (Init.Nat.pred (length l))))) with (length l) by lia. simpl. apply Rle_ge.
    assert (H6 : fold_right Rmult 1 l > 0). { apply fold_right_mult_pos_list_gt_0; auto. }
    assert (H7 : Rpower (fold_right Rmult 1 l) (1 / INR (length l)) > 0). { apply Rpower_gt_0; auto. } 
    assert (H8 : (length l > 0)%nat) by lia.
    pose proof (MaxRlist_In l H8) as H9. pose proof (MinRlist_In l H8) as H10. pose proof H1 as Hpos. unfold pos_list in H1. rewrite Forall_forall in H1.
    assert (H11 : MaxRlist l > 0). { specialize (H1 (MaxRlist l) H9); lra. } assert (H12 : MinRlist l > 0). { specialize (H1 (MinRlist l) H10). lra. }
    assert (H13 : arithmetic_mean l > 0). { apply arithmetic_mean_pos_list; auto. }
    assert (H14 : MaxRlist l > arithmetic_mean l). { apply MaxRlist_gt_arith_mean; auto. } 
    assert (H15 : MinRlist l < arithmetic_mean l). { apply MinRlist_lt_arith_mean; auto. } 
    assert (H16 : pos_list (remove_one Req_dec_T (MaxRlist l) l)). { apply pos_list_remove_one; auto. }
    assert (H17 : pos_list (remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l))). { apply pos_list_remove_one; auto. }
    assert (H18 : fold_right Rmult 1 (remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l)) > 0). { apply fold_right_mult_pos_list_gt_0; auto. }
    assert (H19 : (MaxRlist l + MinRlist l - arithmetic_mean l) > 0). { nra. }
    assert (H20 : arithmetic_mean l * ((MaxRlist l + MinRlist l - arithmetic_mean l) * fold_right Rmult 1 (remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l))) > 0).
    { rewrite <- Rmult_assoc. assert (arithmetic_mean l * (MaxRlist l + MinRlist l - arithmetic_mean l) > 0) by nra. nra. }
    assert (H21 : 0 < Rpower (arithmetic_mean l * ((MaxRlist l + MinRlist l - arithmetic_mean l) * fold_right Rmult 1 (remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l)))) (1 / INR (length l))).
    { apply Rpower_gt_0; auto. }
    assert (H22 : (length (remove_one Req_dec_T (MaxRlist l) l) > 0)%nat). { rewrite remove_one_In_length; auto; lia. }
    assert (H23 : In (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l)). { apply In_remove_one; auto. }

    apply pow_incrst_3 with (n := length l); try lia; auto.
    repeat rewrite <- Rpower_pow; auto. repeat rewrite Rpower_mult. replace (1 / INR (length l) * INR (length l)) with 1. 2 : { field; apply not_0_INR; lia. }
    repeat rewrite Rpower_1; auto. repeat rewrite fold_right_Rmult_remove_one_In; auto; try lra; try lia. 
    assert (H24 : arithmetic_mean l * (MaxRlist l + MinRlist l - arithmetic_mean l) >= MaxRlist l * MinRlist l).
    {
      (*this is not necessary we can just do nra but just to show how the book does it*)
      apply Rle_ge. apply Rplus_le_reg_r with (r := - arithmetic_mean l * (MaxRlist l + MinRlist l - arithmetic_mean l)). field_simplify.
      replace (MaxRlist l * MinRlist l - MaxRlist l * arithmetic_mean l - MinRlist l * arithmetic_mean l + arithmetic_mean l ^ 2) with 
            ((arithmetic_mean l - MinRlist l) * (arithmetic_mean l - MaxRlist l)) by nra. nra.
    }
    assert (H25 : forall a b c d, a > 0 -> b > 0 -> c > 0 -> d > 0 -> b >= d -> a <= d * c -> a <= b * c) by (intros; nra).
    rewrite <- Rmult_assoc.
    apply H25 with (d := MaxRlist l * MinRlist l); auto; try nra. 2 : { field_simplify; nra. } unfold Rdiv.
    assert (H26 : / MaxRlist l > 0). { apply Rinv_pos; nra. } assert (H27 : / MinRlist l > 0). { apply Rinv_pos; nra. } 
    assert (H28 : fold_right Rmult 1 l * / MaxRlist l > 0) by nra. nra.
Qed.

Lemma build_list_for_lemma_2_22_a_unchanged : forall l,
  (Forall (fun x => x = nth 0 l 0) l -> build_list_for_lemma_2_22_a l = l).
Proof.
  intros l H1. unfold build_list_for_lemma_2_22_a. assert (length l = 0 \/ length l > 0)%nat as [H2 | H2] by lia.
  - rewrite H2. simpl. apply length_zero_iff_nil in H2. rewrite H2. reflexivity.
  - assert (length l =? 0 = false)%nat as H3 by (apply Nat.eqb_neq; lia). rewrite H3. destruct (Req_dec_T (MinRlist l) (MaxRlist l)) as [H4 | H4]; auto.
    pose proof (MinRlist_In l H2) as H5. pose proof (MaxRlist_In l H2) as H6. rewrite Forall_forall in H1. specialize (H1 (MinRlist l) H5) as H7. specialize (H1 (MaxRlist l) H6) as H8.
    lra.
Qed.

Lemma In_pos_list : forall l x,
  pos_list l -> In x l -> x > 0.
Proof.
  intros l x H1 H2. unfold pos_list in H1. rewrite Forall_forall in H1. apply H1; auto.
Qed.

Lemma build_list_for_lemma_2_22_a_pos_list : forall l,
  pos_list l -> pos_list (build_list_for_lemma_2_22_a l).
Proof.
  intros l H1. unfold build_list_for_lemma_2_22_a. assert (length l = 0 \/ length l > 0)%nat as [H2 | H2] by lia.
  - rewrite H2. simpl. unfold pos_list. apply Forall_nil.
  - assert (length l =? 0 = false)%nat as H3 by (apply Nat.eqb_neq; lia). rewrite H3. destruct (Req_dec_T (MinRlist l) (MaxRlist l)) as [H4 | H4]; auto.
    unfold pos_list. rewrite Forall_forall. intros x H5. destruct H5 as [H5 | H5].
    -- pose proof arithmetic_mean_pos_list as H6. rewrite <- H5. apply H6; auto. 
    -- destruct H5 as [H5 | H5].
       + pose proof Min_Max_plus_gt_arith_mean l H1 as H6. rewrite <- H5. lra.
       + apply pos_list_remove_one with (x := MaxRlist l) in H1 as H6. apply pos_list_remove_one with (x := MinRlist l) in H6 as H7.
         apply In_pos_list with (l := remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l)) in H5 as H8; auto.
Qed.

Lemma count_occ_forall_eq_nth : forall l : list R,
  Forall (fun x => x = nth 0 l 0) l -> count_occ Req_dec_T l (nth 0 l 0) = length l.
Proof.
  intros l H1. rewrite Forall_forall in H1. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (Req_dec_T h h) as [H2 | H2]; try lra. assert (H3 : forall x, In x t -> x = h).
    { intros x H3. apply H1. right. auto. } assert (length t = 0 \/ length t > 0)%nat as [H4 | H4] by lia.
    -- apply length_zero_iff_nil in H4. rewrite H4. reflexivity.
    -- assert (H5 : In (nth 0 t 0) t). { apply nth_In; lia. } specialize (H3 (nth 0 t 0) H5) as H6. rewrite H6 in IH.
       rewrite IH; auto.
Qed.

Lemma repeat_Forall : forall (x : R) l,
  (length l > 0)%nat -> (Forall (eq x) l <-> l = (repeat x (length l))).
Proof.
  intros x l H1. split.
  {
     intro H2. induction l as [| h t IH].
     - simpl. reflexivity.
     - simpl. assert (length t = 0 \/ length t > 0)%nat as [H3 | H3] by lia.
       -- apply length_zero_iff_nil in H3. rewrite H3. simpl. rewrite Forall_forall in H2. specialize (H2 h). rewrite H2; auto. left. reflexivity.
       -- rewrite IH; auto. rewrite Forall_forall in H2. specialize (H2 h). rewrite H2; auto. rewrite repeat_length. reflexivity. left; auto.
          apply Forall_cons_iff in H2. tauto.
  }
  intros H2. rewrite H2. apply Forall_forall. intros y H3. apply In_repeat in H3; auto.
Qed.

Lemma count_occ_forall_eq : forall l x,
  Forall (eq x) l <-> count_occ Req_dec_T l x = length l.
Proof.
  intros l x. split.
  - intro H1. assert (length l = 0 \/ length l > 0)%nat as [H2 | H2] by lia.
    -- apply length_zero_iff_nil in H2. rewrite H2. simpl. reflexivity.
    -- rewrite <- count_occ_forall_eq_nth. 
        2 : { rewrite Forall_eq_imp_eq_nth; auto. intros y H3. apply Forall_forall. intros z H4. rewrite Forall_forall in H1.
              specialize (H1 z H4) as H5. specialize (H1 y H3). nra. } assert (H3 : In (nth 0 l 0) l). { apply nth_In; lia. }
        rewrite Forall_forall in H1. specialize (H1 (nth 0 l 0) H3). rewrite H1. reflexivity.
  - intro H1. assert (length l = 0 \/ length l > 0)%nat as [H2 | H2] by lia.
    -- apply length_zero_iff_nil in H2. rewrite H2. apply Forall_nil.
    -- rewrite Forall_forall. intros y H3. apply count_occ_unique in H1. apply repeat_Forall in H1; auto.
       rewrite Forall_forall in H1. specialize (H1 y H3). rewrite H1. reflexivity.
Qed.

Lemma count_arithmetic_mean_build_list_2_22_a_eq : forall l,
  (length l > 0)%nat -> MinRlist l = MaxRlist l -> count_occ Req_dec_T (build_list_for_lemma_2_22_a l) (arithmetic_mean l) = length l.
Proof.
  intros l H1 H2. apply MinRlist_eq_MaxRlist in H2; auto. pose proof (build_list_for_lemma_2_22_a_unchanged l H2) as H3. rewrite H3.
  assert (H4 : arithmetic_mean l = nth 0 l 0). { apply arithmetic_mean_all_equal; auto. }
  rewrite H4. apply count_occ_forall_eq_nth; auto.
Qed.

Lemma count_arithmetic_mean_build_list_2_22_a_neq : forall l,
  (length l > 0)%nat -> MinRlist l <> MaxRlist l -> (count_occ Req_dec_T (build_list_for_lemma_2_22_a l) (arithmetic_mean l) > count_occ Req_dec_T l (arithmetic_mean l))%nat.
Proof.
  intros l H1 H2. unfold build_list_for_lemma_2_22_a. assert (length l =? 0 = false)%nat as H3 by (apply Nat.eqb_neq; lia). rewrite H3.
  destruct (Req_dec_T (MinRlist l) (MaxRlist l)) as [H4 | H4]; try lra. 
  replace (arithmetic_mean l :: MaxRlist l + MinRlist l - arithmetic_mean l :: remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l)) with 
          ([arithmetic_mean l] ++ [MaxRlist l + MinRlist l - arithmetic_mean l] ++ remove_one Req_dec_T (MinRlist l) (remove_one Req_dec_T (MaxRlist l) l)) by reflexivity.
  repeat rewrite count_occ_app. simpl. destruct (Req_dec_T (arithmetic_mean l) (arithmetic_mean l)) as [H5 | H5]; try lra.
  destruct (Req_dec_T (MaxRlist l + MinRlist l - arithmetic_mean l) (arithmetic_mean l)) as [H6 | H6].
  - assert (H7 : arithmetic_mean l <> MaxRlist l). { intro H7. apply H2. nra. }
    assert (H8 : arithmetic_mean l <> MinRlist l). { intro H8. apply H2. nra. }
    repeat rewrite count_occ_remove_one_not_eq; auto.
  - assert (H7 : arithmetic_mean l <> MaxRlist l). { intro H7. apply H2. pose proof (MaxRlist_gt_arith_mean l H1 H2) as H8. nra. }
    assert (H8 : arithmetic_mean l <> MinRlist l). { intro H8. apply H2. pose proof (MinRlist_lt_arith_mean l H1 H2) as H9. nra. }
    repeat rewrite count_occ_remove_one_not_eq; auto.
Qed.

Fixpoint f_repeat {A : Type} (n : nat) (f : A -> A) (x : A) : A :=
  match n with
  | 0%nat => x
  | S n' => f (f_repeat n' f x)
  end.

Lemma f_repeat_involution : forall (A : Type) (f : A -> A) (n : nat) (x : A),
  f x = x -> f_repeat n f (x) = x.
Proof.
  intros A f n x H1. induction n as [| n IH].
  - simpl. reflexivity.
  - simpl. rewrite  IH. apply H1.
Qed.

Lemma arithmetic_mean_f_repeat_build_list_for_lemma_2_22_a : forall l n,
  (length l > 0)%nat -> arithmetic_mean (f_repeat n build_list_for_lemma_2_22_a l) = arithmetic_mean l.
Proof.
  intros l n H1. generalize dependent l. induction n as [| k IH].
  - intros l H1. simpl. reflexivity.
  - intros l H1. simpl. rewrite arithmetic_mean_build_list_2_22_a_equiv. apply IH; auto.
Qed.

Lemma f_repeat_all_count_occ_lemma_2_22_helper : forall (l : list R) (n : nat) (f : list R -> list R) (g : list R -> R),
  (length l > 0)%nat ->
  (forall l, length l = length (f l)) ->
  (forall l, ~Forall (eq (g l)) l -> 
     (count_occ Req_dec_T (f l) (g l) > count_occ Req_dec_T l (g l))%nat) ->
  (forall l, Forall (eq (g l)) l -> f l = l) ->
  (length l > n)%nat ->
  (forall l, g (f l) = g l) ->
  (forall l x, (length l > 0)%nat -> Forall (eq x) l -> x = g l) ->
  (forall l, g (f_repeat n f l) = g l) ->
  (forall l, length (f_repeat n f l) = length l) ->
  (count_occ Req_dec_T (f_repeat n f l) (g l) >= n)%nat.
Proof.
  intros l n f g H1 H2 H3 H4 H5 H6 H7 H8 H9. generalize dependent l. induction n as [| k IH].
  - intros l H10 H11. lia.
  - intros l H10 H11. simpl. assert (Forall (eq (g l)) l \/ ~Forall (eq (g l)) l) as [H12 | H12] by apply classic.
    -- rewrite f_repeat_involution. rewrite (H4 l); auto. apply count_occ_forall_eq in H12; auto; lia. apply (H4 l); auto.
    -- assert ((Forall (eq (g l)) (f_repeat k f l)) \/ ~(Forall (eq (g l)) (f_repeat k f l))) as [H13 | H13] by apply classic.
       + assert (H14 : g (f_repeat k f l) = g l). { specialize (H8 l). simpl in H8. rewrite H6 in H8. auto. }
         assert (H15 : length (f_repeat k f l) = length l). { specialize (H9 l). simpl in H9. rewrite <- H2 in H9. auto. }
         rewrite H4; auto. 2 : { rewrite H14; auto. } apply count_occ_forall_eq in H13; auto. rewrite H15 in H13. lia.
       + specialize (H3 (f_repeat k f l)) as H14. specialize (H8 l) as H15. simpl in H15. rewrite H6 in H15. rewrite H15 in H14. specialize (H14 H13).
         assert (count_occ Req_dec_T (f_repeat k f l) (g l) >= k)%nat as H16.
        { apply IH; auto; try lia. intro l2. specialize (H8 l2) as H16. simpl in H16. rewrite H6 in H16. rewrite H16. auto. intros l2.
          specialize (H9 l2) as H16. simpl in H16. rewrite <- H2 in H16. auto. }
          assert (count_occ Req_dec_T (f l) (g l) > count_occ Req_dec_T l (g l))%nat as H17. { apply H3; auto. } lia.
Qed.

Lemma f_repeat_build_list_for_lemma_2_22_a_nil : forall n,
  f_repeat n build_list_for_lemma_2_22_a [] = [].
Proof.
  intros n. induction n as [| n IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma length_f_repeat_length_build_list_for_lemma_2_22_a : forall l n,
  length (f_repeat (n) build_list_for_lemma_2_22_a l) = length l.
Proof.
  intros l n. generalize dependent l. induction n as [| n IH].
  - intros l. simpl. reflexivity.
  - intros l. simpl. rewrite build_list_for_lemma_2_22_a_length. apply IH.
Qed.

Lemma count_occ_f_repeat_build_list_for_lemma_2_22_a_n_minus_1 : forall l,
  (count_occ Req_dec_T (f_repeat (length l - 1) build_list_for_lemma_2_22_a l) (arithmetic_mean l) >= length l - 1)%nat.
Proof.
  intros l. assert (length l = 0 \/ length l > 0)%nat as [H1 | H1] by lia.
  - apply length_zero_iff_nil in H1. rewrite H1. simpl. lia.
  - apply f_repeat_all_count_occ_lemma_2_22_helper; auto; try lia.
    -- intros l2. rewrite build_list_for_lemma_2_22_a_length; auto.
    -- intros l2 H2. assert (length l2 = 0 \/ length l2 > 0)%nat as [H3 | H3] by lia.
       + apply length_zero_iff_nil in H3. rewrite H3 in H2. rewrite arithmetic_mean_nil in H2. exfalso. apply H2. apply Forall_nil.
       + apply count_arithmetic_mean_build_list_2_22_a_neq; auto. assert (MinRlist l2 = MaxRlist l2 \/ MinRlist l2 <> MaxRlist l2) as [H4 | H4] by apply classic; auto.
         rewrite <- MinRlist_eq_MaxRlist_eq_arith_mean in H2; auto. apply MinRlist_neq_MaxRlist in H2; auto.
    -- intros l2 H2. apply build_list_for_lemma_2_22_a_unchanged; auto. assert (length l2 = 0 \/ length l2 > 0)%nat as [H3 | H3] by lia.
       + apply length_zero_iff_nil in H3. rewrite H3. apply Forall_nil.
       + apply Forall_eq_imp_eq_nth; auto. intros y H4. apply Forall_forall. intros z H5. rewrite Forall_forall in H2. specialize (H2 z H5) as H6.
         specialize (H2 y H4) as H7. nra.
    -- intros l2. apply arithmetic_mean_build_list_2_22_a_equiv.
    -- intros l2 x H2 H3. apply eq_sym. apply arithmetic_mean_all_equal with (l := l2); auto. apply Forall_forall. intros y H4.
       rewrite Forall_forall in H3. specialize (H3 y H4) as H5. auto.
    -- intros l2. assert (length l2 = 0 \/ length l2 > 0)%nat as [H2 | H2] by lia.
       + apply length_zero_iff_nil in H2. rewrite H2. simpl. rewrite f_repeat_build_list_for_lemma_2_22_a_nil. reflexivity.
       + apply arithmetic_mean_f_repeat_build_list_for_lemma_2_22_a; auto.
    -- intros l2. rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; auto.
Qed.

Lemma count_occ_f_repeat_build_list_for_lemma_2_22_a_n : forall l,
  (count_occ Req_dec_T (f_repeat (length l) build_list_for_lemma_2_22_a l) (arithmetic_mean l) = length l)%nat.
Proof.
  intros l. assert (length l = 0 \/ length l > 0)%nat as [H1 | H1] by lia.
  - apply length_zero_iff_nil in H1. rewrite H1. simpl. reflexivity.
  - destruct (length l) as [| n] eqn: H2; try lia.
    simpl. assert (count_occ Req_dec_T (f_repeat n build_list_for_lemma_2_22_a l) (arithmetic_mean l) >= n)%nat as H3.
    { replace n with (length l - 1)%nat by lia. apply count_occ_f_repeat_build_list_for_lemma_2_22_a_n_minus_1. }
    set (l2 := f_repeat n build_list_for_lemma_2_22_a l).
    assert (MinRlist l2 = MaxRlist l2 \/ MinRlist l2 <> MaxRlist l2) as [H4 | H4] by apply classic.
    -- apply count_arithmetic_mean_build_list_2_22_a_eq in H4.
       2 : { unfold l2. rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; lia. }
       rewrite <- H2. replace (length l) with (length l2) by (unfold l2; rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; lia).
       replace (arithmetic_mean l) with (arithmetic_mean l2) by (unfold l2; apply arithmetic_mean_f_repeat_build_list_for_lemma_2_22_a; lia). lia.
    -- apply count_arithmetic_mean_build_list_2_22_a_neq in H4; auto.
       2 : { unfold l2. rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; lia. }
       rewrite <- H2. replace (length l) with (length l2) by (unfold l2; rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; lia).
       replace (f_repeat n build_list_for_lemma_2_22_a l) with l2 in H3 by reflexivity.
       replace (arithmetic_mean l) with (arithmetic_mean l2) in H3 by (unfold l2; apply arithmetic_mean_f_repeat_build_list_for_lemma_2_22_a; lia).
       assert ((count_occ Req_dec_T l2 (arithmetic_mean l2) = n)%nat \/ (count_occ Req_dec_T l2 (arithmetic_mean l2) > n)%nat) as [H5 | H5] by lia.
       + rewrite H5 in H4. replace (length l2) with (length l) by (unfold l2; rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; lia).
         rewrite H2. replace (arithmetic_mean l) with (arithmetic_mean l2) by (unfold l2; apply arithmetic_mean_f_repeat_build_list_for_lemma_2_22_a; lia).
         assert ((count_occ Req_dec_T (build_list_for_lemma_2_22_a l2) (arithmetic_mean l2) <= S n))%nat as H6.
         { rewrite <- H2. replace (length l) with (length (build_list_for_lemma_2_22_a l2)). 
            2 : { unfold l2. rewrite build_list_for_lemma_2_22_a_length. rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; lia. }
            apply count_occ_bound. } lia.
      + replace (length l2) with (length l) by (unfold l2; rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; lia).
         rewrite H2. replace (arithmetic_mean l) with (arithmetic_mean l2) by (unfold l2; apply arithmetic_mean_f_repeat_build_list_for_lemma_2_22_a; lia).
         assert ((count_occ Req_dec_T (build_list_for_lemma_2_22_a l2) (arithmetic_mean l2) <= S n))%nat as H6.
         { rewrite <- H2. replace (length l) with (length (build_list_for_lemma_2_22_a l2)). 
            2 : { unfold l2. rewrite build_list_for_lemma_2_22_a_length. rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; lia. }
            apply count_occ_bound. } lia.
Qed.

Lemma f_repeat_build_list_for_lemma_2_22_a_all_equal : forall l,
  Forall (eq (arithmetic_mean l)) (f_repeat (length l) build_list_for_lemma_2_22_a l).
Proof.
  intros l. assert (length l = 0 \/ length l > 0)%nat as [H1 | H1] by lia. 
  - apply length_zero_iff_nil in H1. rewrite H1. simpl. apply Forall_nil.
  - apply count_occ_forall_eq. rewrite count_occ_f_repeat_build_list_for_lemma_2_22_a_n; auto. rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; auto.
Qed.

Lemma all_eq_arithmetic_mean : forall l x,
  (length l > 0)%nat -> Forall (eq x) l -> arithmetic_mean l = x.
Proof.
  intros l x H1 H2. apply arithmetic_mean_all_equal; auto. apply Forall_forall. intros y H3. rewrite Forall_forall in H2. specialize (H2 y H3). auto.
Qed.

Lemma f_repeat_build_list_for_lemma_2_22_a_repeat_arithmetic_mean : forall l,
  f_repeat (length l) build_list_for_lemma_2_22_a l = repeat (arithmetic_mean l) (length l).
Proof.
  intros l. assert (length l = 0 \/ length l > 0)%nat as [H1 | H1] by lia.
  - apply length_zero_iff_nil in H1. rewrite H1. simpl. reflexivity.
  - pose proof (f_repeat_build_list_for_lemma_2_22_a_all_equal l) as H2. apply repeat_Forall in H2.
    -- rewrite length_f_repeat_length_build_list_for_lemma_2_22_a in H2. auto.
    -- rewrite length_f_repeat_length_build_list_for_lemma_2_22_a; auto.
Qed.

Lemma pos_list_f_repeat_build_list_for_lemma_2_22_a : forall l n,
  pos_list l -> pos_list (f_repeat n build_list_for_lemma_2_22_a l).
Proof.
  intros l n H1. induction n as [| n IH].
  - simpl. auto.
  - simpl. apply build_list_for_lemma_2_22_a_pos_list; auto.
Qed.

Lemma geometric_mean_f_repeat_build_list_for_lemma_2_22_a : forall l n,
  pos_list l ->
  geometric_mean (f_repeat (n) build_list_for_lemma_2_22_a l) >= geometric_mean l.
Proof.
  intros l n H1. induction n as [| n IH].
  - simpl. lra.
  - simpl. pose proof (geometric_mean_build_list_2_22_a_lt (f_repeat n build_list_for_lemma_2_22_a l)) as H2.
    apply Rge_trans with (r2 := geometric_mean (f_repeat n build_list_for_lemma_2_22_a l)); auto. apply H2. apply pos_list_f_repeat_build_list_for_lemma_2_22_a; auto.
Qed.

Lemma lemma_2_22_a'' : forall l,
  pos_list l -> geometric_mean l <= arithmetic_mean l.
Proof.
  intros l H1. assert (length l = 0 \/ length l > 0)%nat as [H2 | H2] by lia.
  - apply length_zero_iff_nil in H2. rewrite H2. rewrite arithmetic_mean_nil, geometric_mean_nil. lra.
  - assert (Forall (fun x => x = nth 0 l 0) l \/ ~Forall (fun x => x = nth 0 l 0) l) as [H3 | H3] by apply classic.
    -- rewrite arithmetic_mean_all_equal with (r := nth 0 l 0); auto. rewrite geometric_mean_all_equal with (r := nth 0 l 0); auto. lra.
    -- pose proof (geometric_mean_f_repeat_build_list_for_lemma_2_22_a l (length l) H1) as H4.
       rewrite f_repeat_build_list_for_lemma_2_22_a_repeat_arithmetic_mean in H4. rewrite geometric_mean_repeat in H4; auto; try lia; try nra.
       apply arithmetic_mean_pos_list; auto.
Qed.

Lemma lemma_2_22_b : forall (l : list R) k,
  pos_list l ->
    (length l = 2 ^ k)%nat -> geometric_mean l <= arithmetic_mean l.
Proof.
  intros l k H1 H2. generalize dependent l. induction k as [| k IH].
  - intros l H1 H2. simpl in H2. unfold geometric_mean, arithmetic_mean. rewrite H2.
    simpl. replace (1 / 1) with 1 by lra. rewrite Rpower_1. 2 : { apply fold_right_mult_pos_list_gt_0. apply H1. } 
    replace (fold_right Rplus 0 l / 1) with (fold_right Rplus 0 l) by lra. assert (H3 : exists a, l = [a]). 
    { destruct l. inversion H2. exists r. inversion H2 as [H3]. apply length_zero_iff_nil in H3. rewrite H3. reflexivity. }
    destruct H3 as [a H3]. rewrite H3. simpl. nra.
  - intros l H1 H2. set (l1 := firstn (length l / 2) l). set (l2 := skipn (length l / 2) l).
    assert (H3 : l1 ++ l2 = l). { unfold l1, l2. rewrite firstn_skipn. reflexivity. }
    assert (H4 : (length l1 = 2 ^ k)%nat).
    { unfold l1. rewrite H2. replace (2 ^ S k)%nat with (2 * 2 ^ k)%nat. 2 : { simpl. lia. }
      rewrite Nat.mul_comm. rewrite Nat.div_mul. 2 : { lia. } rewrite firstn_length. rewrite H2. 
      simpl. lia. }
    assert (H5 : (length l2 = 2^k)%nat).
    { unfold l2. rewrite H2. replace (2^S k)%nat with (2 * 2^k)%nat by (simpl; lia).
      rewrite Nat.mul_comm. rewrite Nat.div_mul by lia. rewrite skipn_length. rewrite H2.
      simpl. lia. }
    rewrite <- H3 at 1. rewrite geometric_mean_app. 2 : { rewrite <- H3 in H1. apply pos_list_app_iff in H1. tauto. }
    2 : { rewrite <- H3 in H1. apply pos_list_app_iff in H1. tauto. }
    2 : { lia. }
    assert (H6 : (0 < length l1)%nat). { rewrite H4. apply pow_2_n_gt_0. }
    assert (H7 : (0 < length l2)%nat). { rewrite H5. apply pow_2_n_gt_0. }
    assert (pos_list l1 /\ pos_list l2) as [H8 H9]. { rewrite <- H3 in H1. apply pos_list_app_iff in H1. tauto. }
    assert (H10 : sqrt (geometric_mean l1 * geometric_mean l2) <= (geometric_mean l1 + geometric_mean l2) / 2).
    { apply ge_le_arith_2. unfold geometric_mean. destruct (length l1). lia. simpl. apply Rpower_gt_0. apply fold_right_mult_pos_list_gt_0. auto.
      unfold geometric_mean. destruct (length l2). lia. simpl. apply Rpower_gt_0. apply fold_right_mult_pos_list_gt_0. auto. }
    assert ((geometric_mean l1 <= arithmetic_mean l1) /\ (geometric_mean l2 <= arithmetic_mean l2)) as [H11 H12].
    { split; apply IH; auto. }
    assert (H13 : sqrt (geometric_mean l1 * geometric_mean l2) <= (arithmetic_mean l1 + arithmetic_mean l2) / 2) by nra.
    assert (H14 : (arithmetic_mean l1 + arithmetic_mean l2) / 2 = arithmetic_mean l).
    { unfold arithmetic_mean. replace ((fold_right Rplus 0 l1 / INR (length l1) + fold_right Rplus 0 l2 / INR (length l2)) / 2) with
      ((fold_right Rplus 0 l1 + fold_right Rplus 0 l2) / (2 * INR (length l1))). 2 : { assert (H14 : INR (length l1) <> 0). { apply not_0_INR. nia. } 
      assert (H15 : length l1 = length l2). { nia. } rewrite <- H15. field; nra. }
    rewrite <- fold_right_plus_app. rewrite H3. rewrite H2. rewrite H4. simpl. rewrite Nat.add_0_r. 
    rewrite plus_INR. replace (2 * INR (2 ^ k)) with (INR (2 ^ k) + INR (2 ^ k)) by (simpl; lra). reflexivity. }
    nra.
Qed.

Lemma exists_pow_2_gt_n : forall n,
  exists m, (2 ^ m > n)%nat.
Proof.
  intros n. induction n as [| n' IH].
  - exists 1%nat. simpl. lia.
  - destruct IH as [m IH]. exists (S m). simpl. lia.
Qed.

Lemma pos_list_arith_mean_gt_0 : forall l,
  pos_list l -> (length l > 0)%nat -> arithmetic_mean l > 0.
Proof.
  intros l H1 H2. unfold arithmetic_mean. apply Rdiv_lt_0_compat. apply Rgt_lt.
  apply fold_right_plus_pos_list_gt_0; auto. apply lt_0_INR. auto.
Qed.

Lemma pos_list_repeat : forall a n,
  a > 0 -> pos_list (repeat a n).
Proof.
  intros a n H1. unfold pos_list. apply Forall_forall. intros x H2. apply repeat_spec in H2. lra.
Qed.

Lemma pow_minus : forall a b c,
  a > 0 -> (b > 0)%nat -> (c > 0)%nat -> (b >= c)%nat -> a ^ (b - c) = a ^ b / a ^ c.
Proof.
  intros a b c H1 H2 H3 H4. induction c as [| c' IH].
  - simpl. unfold Rdiv. rewrite Rinv_1. rewrite Rmult_1_r. rewrite Nat.sub_0_r. reflexivity.
  - simpl. replace (a^b / (a * a^c')) with (a^b / a^c' * / a). 2 : { field. split. apply pow_nonzero. lra. lra. }
    assert (c' = 0 \/ c' > 0)%nat as [H5 | H5] by lia.
    -- rewrite H5. simpl. unfold Rdiv. rewrite Rinv_1. rewrite Rmult_1_r. destruct b.
      --- lia.
      --- simpl. rewrite Nat.sub_0_r. field. lra.
    -- rewrite <- IH. 2 : { lia. } 2 : { lia. } replace (b - c')%nat with (S (b - S c'))%nat by lia. simpl. field. lra.
Qed.

Lemma Rle_pow_base : forall a b n,
  0 < a -> 0 < b -> (n > 0)%nat -> a^n <= b^n -> a <= b.
Proof.
  intros a b n H1 H2 H3 H4. induction n as [| k IH].
  - lia.
  - simpl in H4. destruct k.
    -- simpl in H4. lra.
    -- apply IH. lia. simpl. simpl in H4. pose proof Rtotal_order a b as [H5 | [H6 | H7]].
      --- assert (H6 : a^k <= b^k). { apply pow_incr. lra. } assert (H7 : a^k > 0). { apply pow_lt. lra. } nra.
      --- rewrite H6. lra.
      --- assert (H8 : b^k <= a^k). { apply pow_incr. lra. } assert (H9 : b^k > 0). { apply pow_lt. lra. }
          assert (H10 : a * a^k > b * b^k). { nra. } assert (H11 : a * (a * a^k) > b * (b * b^k)). { apply Rmult_gt_0_lt_compat. nra. nra. nra. nra. } nra.
Qed.

Lemma lemma_2_22_c : forall (l : list R),
  pos_list l -> geometric_mean l <= arithmetic_mean l.
Proof.
  intros l H1. pose proof exists_pow_2_gt_n (length l) as [m H2]. 
  set (l2 := repeat (arithmetic_mean l) (2^m - length l)). set (l3 := l ++ l2).
  assert (length l = 0 \/ length l > 0)%nat as [H3 | H3] by lia.
  - unfold geometric_mean, arithmetic_mean. apply length_zero_iff_nil in H3. rewrite H3. simpl. lra.
  - assert (H4 : arithmetic_mean l > 0). { apply pos_list_arith_mean_gt_0; auto. }
    assert (H5 : pos_list l2). { unfold l2. apply pos_list_repeat. apply H4. }
    assert (H6 : pos_list l3). { unfold l3. apply pos_list_app_iff. split; auto. }
    assert (H7 : (length l3 = 2 ^ m)%nat). { unfold l3, l2. rewrite app_length. rewrite repeat_length. lia. }
    assert (H8 : (length l3 > 0)%nat). { rewrite H7. apply pow_2_n_gt_0. }
    assert (H9 : geometric_mean l3 <= arithmetic_mean l3). { apply lemma_2_22_b with (k := m); auto. }
    unfold geometric_mean, arithmetic_mean in H9. destruct (Nat.eq_dec (length l3) 0) as [H10 | H10].
    -- lia.
    -- rewrite H7 in H9. pose proof Rle_Rpower_l (Rpower (fold_right Rmult 1 l3) (1 / INR (2 ^ m))) (fold_right Rplus 0 l3 / INR (2 ^ m)) (INR 2^m) as H11.
       assert (H12 : 0 <= INR 2 ^ m).
       { replace (INR 2) with 2 by (simpl; lra). assert (0 <= 2^m)%nat by lia. apply le_INR in H. 
         replace (INR 0) with 0 in H by (simpl; lra). replace (INR (2^m)) with (2^m) in H. 2 : { rewrite pow_INR. replace (INR 2) with 2 by (simpl; lra). reflexivity. } lra. }
       apply H11 in H12. 2 : { split. apply Rpower_gt_0. apply fold_right_mult_pos_list_gt_0. auto. auto. }
       rewrite Rpower_mult in H12. replace (1 / INR (2 ^ m) * INR (2)^m) with 1 in H12. 2 : { rewrite <- pow_INR. field. apply not_0_INR. lia. }
       rewrite Rpower_1 in H12. 2 : { apply Rgt_lt. apply fold_right_mult_pos_list_gt_0; auto. }
       replace (INR 2 ^ m) with (INR (2^m)) in H12. 2 : { rewrite pow_INR. replace (INR 2) with 2 by (simpl; lra). reflexivity. }
       rewrite Rpower_pow in H12. 2 : { apply Rdiv_pos_pos. apply fold_right_plus_pos_list_gt_0; auto. apply lt_0_INR. lia. }
       unfold l3 in H12 at 2. rewrite fold_right_plus_app in H12. replace (fold_right Rplus 0 l) with (arithmetic_mean l * INR (length l)) in H12.
       2 : { unfold arithmetic_mean. field. apply not_0_INR. lia. } replace (fold_right Rplus 0 l2) with (arithmetic_mean l * (INR (2^m) - INR (length l))) in H12.
       2 : { unfold l2. rewrite fold_right_plus_repeat. rewrite minus_INR; try lia; nra. }
       replace ((arithmetic_mean l * INR (length l) + arithmetic_mean l * (INR (2^m) - INR (length l))) / INR (2^m)) with (arithmetic_mean l) in H12.
       2 : { field. apply not_0_INR. lia. } unfold l3 in H12. rewrite fold_right_mult_app_R in H12. replace (fold_right Rmult 1 l2) with (arithmetic_mean l ^ (2^m - length l)) in H12.
       2 : { unfold l2. rewrite fold_right_mult_repeat. reflexivity. }
       assert (H13 : arithmetic_mean l ^ 2 ^ m / (arithmetic_mean l ^ (2 ^ m - length l)) = arithmetic_mean l ^ length l).
       { rewrite pow_minus. 2 : { apply pos_list_arith_mean_gt_0; auto. } 2 : { lia. } 2 : { lia. } 2 : { lia. } field; split; apply pow_nonzero; auto; try lra. }
       assert (H14 : 0 < arithmetic_mean l ^ (2 ^ m - length l)). { apply pow_lt. apply pos_list_arith_mean_gt_0; auto. }
       assert (H15 : fold_right Rmult 1 l <= arithmetic_mean l ^ 2 ^ m / (arithmetic_mean l ^ (2 ^ m - length l))). 
       { apply Rmult_le_compat_r with (r := / arithmetic_mean l ^ (2 ^ m - length l)) in H12. 2 : { apply Rlt_le. apply Rinv_pos. lra. }
         rewrite Rmult_assoc in H12. rewrite Rinv_r in H12. 2 : { lra. } unfold Rdiv in H13. rewrite H13 in H12. rewrite Rmult_1_r in H12. lra. }
       rewrite H13 in H15. unfold geometric_mean, arithmetic_mean. destruct (Nat.eq_dec (length l) 0) as [H16 | H16].
       --- lia.
       --- apply Rle_pow_base with (n := length l); auto. apply Rpower_gt_0. apply fold_right_mult_pos_list_gt_0; auto.
           rewrite <- Rpower_pow. 2 : { apply Rpower_gt_0. apply fold_right_mult_pos_list_gt_0; auto. } rewrite Rpower_mult.
           replace (1 / INR (length l) * INR (length l)) with 1. 2 : { field. apply not_0_INR. lia. } rewrite Rpower_1. 2 : { apply fold_right_mult_pos_list_gt_0; auto. }
           unfold arithmetic_mean in H15. nra.
Qed.

Lemma lemma_2_23_a : forall (a : R) (n m : nat),
  a ^ (n + m) = a^n * a^m.    
Proof.
  intros a n m. induction n as [| k IH].
  - simpl. lra.
  - replace (a ^ (S k + m)) with (a * (a ^ (k + m))) by (simpl; lra).
    rewrite IH. replace (a ^ S k) with (a * a ^ k) by (simpl; lra). lra.
Qed.

Lemma lemma_2_23_b : forall (a : R) (n m : nat),
  (a ^ n) ^ m = a ^ (n * m).
Proof.
  intros a n m. induction m as [| k IH].
  - simpl. rewrite Nat.mul_0_r. lra.
  - simpl. rewrite IH. rewrite <- lemma_2_23_a. 
    replace (n * S k)%nat with (n + n * k)%nat by lia. reflexivity.
Qed.

Open Scope nat_scope.

Lemma lemma_2_24_a : forall a b c,
  a * (b + c) = a * b + a * c.
Proof.
  intros a b c. induction a as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma lemma_2_24_b : forall a,
  a * 1 = a.
Proof.
  intros a. induction a as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma lemma_2_24_c : forall a b,
  a * b = b * a.
Proof.
  intros a b. induction b as [| k IH].
  - simpl. rewrite Nat.mul_0_r. reflexivity.
  - simpl. rewrite <- IH. rewrite <- lemma_2_24_b with (a := a) at 2. rewrite <- lemma_2_24_a.
    simpl. reflexivity.
Qed.

Close Scope nat_scope.

Definition Inductive (A : R -> Prop) : Prop :=
  A 1 /\ forall r : R, A r -> A (r + 1).

Definition Natural (r : R) : Prop :=
  forall A, Inductive A -> A r.

Lemma lemma_2_25_a_i : Inductive (fun r => True).
Proof.
  split; auto.
Qed.

Lemma lemma_2_25_a_ii : Inductive (fun r => r > 0).
Proof.
  split; intros; nra.
Qed.

Lemma lemma_2_25_a_iii : Inductive (fun r => r <> 1 / 2 /\ r > 0).
Proof.
  split; intros; nra.
Qed.

Lemma lemma_2_25_a_iv : ~Inductive (fun r => r > 0 /\ r <> 5).
Proof.
  intros [[H1 H2] H3]. specialize (H3 4). nra.
Qed.

Lemma lemma_2_25_a_v : forall (A B : R -> Prop),
  Inductive A /\ Inductive B -> Inductive (fun r => A r /\ B r).
Proof.
  intros A B [[H1 H2] [H3 H4]]. split.
  - auto.
  - intros r [H5 H6]. split; auto.
Qed.

Lemma lemma_2_25_b_i : Natural 1.
Proof.
  intros A [H1 H2]. auto.
Qed.

Lemma lemma_2_25_b_ii : forall k,
  Natural k -> Natural (k + 1).
Proof.
  intros k H1 A [H2 H3]. apply H3. apply H1. split; auto.
Qed.

Open Scope nat_scope.

Definition towers := (list nat * list nat * list nat)%type.

Definition tower1 (t : towers) : list nat := match t with (l, _, _) => l end.
Definition tower2 (t : towers) : list nat := match t with (_, l, _) => l end.
Definition tower3 (t : towers) : list nat := match t with (_, _, l) => l end.

Definition tower_idx := nat.

Definition get_tower (t : towers) (idx : tower_idx) : list nat :=
  match idx with
  | 1 => tower1 t
  | 2 => tower2 t
  | 3 => tower3 t
  | _ => []
  end.

Definition set_tower (t : towers) (idx : tower_idx) (new_tower : list nat) : towers :=
  match idx with
  | 1 => (new_tower, tower2 t, tower3 t)
  | 2 => (tower1 t, new_tower, tower3 t)
  | 3 => (tower1 t, tower2 t, new_tower)
  | _ => t
  end.

Definition valid_start_state (t : towers) (start_pole : tower_idx) : Prop :=
  Sorted lt (get_tower t start_pole) /\
  (forall p, p <> start_pole -> get_tower t p = []).

Definition valid_state (t : towers) : Prop :=
  Sorted lt (tower1 t) /\ Sorted lt (tower2 t) /\ Sorted lt (tower3 t).

Definition valid_stop_state (t : towers) (end_pole : tower_idx) : Prop :=
  (forall p, p <> end_pole -> get_tower t p = []) /\
  Sorted lt (get_tower t end_pole).

Inductive move : Type :=
  | Move (from_pole to_pole : tower_idx).

Definition valid_move (m : move) (t : towers) : bool :=
  match m with
  | Move from_pole to_pole =>
      let src := get_tower t from_pole in
      let dst := get_tower t to_pole in
      match src with
      | [] => false
      | h1 :: _ =>
          match dst with
          | [] => true
          | h2 :: _ => h1 <? h2
          end
      end
  end.

Definition apply_move (m : move) (t : towers) : towers :=
  match m with
  | Move from_pole to_pole =>
      if valid_move m t then
        let src := get_tower t from_pole in
        let dst := get_tower t to_pole in
        let h := hd 0 src in
        let src' := tl src in
        let dst' := h :: dst in
        let t' := set_tower t from_pole src' in
        set_tower t' to_pole dst'
      else t
  end.

Fixpoint apply_moves (l : list move) (t : towers) : towers := 
  match l with
  | [] => t
  | x :: xs => apply_moves xs (apply_move x t)
  end.

Lemma hanoi_solvable (n : nat) (start_pole end_pole : tower_idx) :
  start_pole <> end_pole /\
  exists moves_list : list move,
    let initial_state := set_tower ([], [], []) start_pole (seq 1 n) in
    let final_state := apply_moves moves_list initial_state in
    valid_start_state initial_state start_pole /\
    valid_stop_state final_state end_pole.
Proof.

Admitted.