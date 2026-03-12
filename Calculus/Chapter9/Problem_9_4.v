From Calculus.Chapter9 Require Import Prelude.
From Lib Require Import Binomial Sums.
Open Scope R_scope.

Lemma limit_sum_h : forall m n c,
  (m <= n)%nat ->
  ⟦ lim 0 ⟧ (fun h => sum_f m n (fun j => c j * h ^ (j - m))) = c m.
Proof.
  intros m n. revert m.
  induction n as [| n' IH].
  - intros m c H1. assert (m = 0%nat) as H2 by lia. subst m.
    replace (fun h : R => sum_f 0 0 (fun j => c j * h ^ (j - 0))) with (fun h : R => c 0%nat).
    + apply limit_const.
    + extensionality h. rewrite sum_f_n_n. replace (0 - 0)%nat with 0%nat by lia. simpl. lra.
  - intros m c H1. assert (m = S n' \/ m <= n')%nat as [H2 | H2] by lia.
    + subst m. replace (fun h : R => sum_f (S n') (S n') (fun j => c j * h ^ (j - S n'))) with (fun h : R => c (S n')).
      * apply limit_const.
      * extensionality h. rewrite sum_f_n_n. replace (S n' - S n')%nat with 0%nat by lia. simpl. lra.
    + apply limit_eq' with (f1 := fun h : R => sum_f m n' (fun j => c j * h ^ (j - m)) + c (S n') * h ^ (S n' - m)).
      * intros h. rewrite sum_f_i_Sn_f; try lia. reflexivity.
      * assert (c m = c m + c (S n') * 0 ^ (n' - m) * 0) as H3 by lra. rewrite H3.
        apply limit_plus.
        -- apply IH. lia.
        -- replace (S n' - m)%nat with (S (n' - m))%nat by lia.
           apply limit_eq' with (f1 := fun h : R => c (S n') * h ^ (n' - m) * h).
           ++ intros h. simpl. lra.
           ++ apply limit_mult.
              ** apply limit_mult. apply limit_const. apply limit_pow. apply limit_id.
              ** apply limit_id.
Qed.

Lemma lemma_9_4 : forall n S S',
  S = (fun x => x ^ n) -> ⟦ der ⟧ S = S' -> forall x, S' x = INR n * x ^ (n - 1).
Proof.
  intros n S S' H1 H2 x. subst S. pose proof (H2 x) as H3. unfold derivative_at in H3.
  apply limit_unique with (f := fun h => ((x + h) ^ n - x ^ n) / h) (a := 0).
  - apply H3.
  - assert (n = 0%nat \/ (n >= 1)%nat) as [H4 | H4] by lia.
    + subst n. apply limit_eq' with (f1 := fun h => 0).
      * intros h. lra.
      * replace (INR 0 * x ^ (0 - 1)%nat) with 0 by (simpl; lra). apply limit_const.
    + apply limit_eq with (f1 := fun h => sum_f 1 n (fun j => INR (choose n j) * x ^ (n - j) * h ^ (j - 1))).
      * exists 1. split. lra. intros h H_neq. pose proof Binomial_Theorem x h n as H5.
        rewrite sum_f_Si in H5; try lia.
        replace (INR (choose n 0) * x ^ (n - 0)%nat * h ^ 0) with (x ^ n) in H5.
        2 : { replace (n - 0)%nat with n by lia. rewrite n_choose_0. simpl (h ^ 0). rewrite Rmult_1_l. rewrite Rmult_1_r. reflexivity. }
        replace (sum_f 1 n (fun i : nat => (INR (choose n i) * x ^ (n - i)) * h ^ i)) with (h * sum_f 1 n (fun i : nat => (INR (choose n i) * x ^ (n - i)) * h ^ (i - 1))) in H5.
        2 : {
           rewrite r_mult_sum_f_i_n_f. apply sum_f_equiv. lia.
           intros i H7. assert (i = 0%nat \/ (i >= 1)%nat) as [H8 | H8] by lia; try lia.
           pose proof Binomial_R.pow_equ h i H8 as H9. rewrite H9. lra.
        }
        rewrite H5.
        set (S_sum := sum_f 1 n (fun i : nat => (INR (choose n i) * x ^ (n - i)) * h ^ (i - 1))).
        unfold Rdiv. assert (h = 0 \/ h <> 0) as [H6 | H6] by lra.
        -- subst h. replace (0 - 0) with 0 in H_neq by lra. rewrite Rabs_R0 in H_neq. lra.
        -- replace (h * S_sum + x ^ n - x ^ n) with (h * S_sum) by lra.
           assert (Halg: (h * S_sum) * / h = S_sum).
           { rewrite (Rmult_comm (h * S_sum) (/ h)). rewrite <- Rmult_assoc. rewrite Rinv_l. apply Rmult_1_l. lra. }
           symmetry. exact Halg.
      * replace (INR n * x ^ (n - 1)) with (INR (choose n 1) * x ^ (n - 1)).
        -- apply limit_eq' with (f1 := fun h => sum_f 1 n (fun j : nat => (INR (choose n j) * x ^ (n - j)) * h ^ (j - 1))).
           ++ intros h. apply sum_f_equiv. lia. intros i H7. lra.
           ++ apply limit_sum_h. lia.
        -- rewrite n_choose_1. reflexivity.
Qed.
