From Calculus.Chapter2 Require Import Prelude.

Lemma lemma_2_5_a : forall n r,
  r <> 1 -> ∑ 0 n (fun i => r ^ i) = (1 - r ^ (n+1)) / (1 - r).
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
  r <> 1 -> ∑ 0 n (fun i => r ^ i) = (1 - r ^ (n+1)) / (1 - r).
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