From Lib Require Import Imports Sums Binomial.
From Calculus Require Import Problem_2_3.
Import Binomial_R Choose_R_Notations.
Open Scope R_scope.

Lemma lemma_2_4_a : forall l m n,
  ∑ 0 l (fun i => n ∁ i * m ∁ (l - i)) = (n + m) ∁ l.
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

Lemma lemma_2_4_b : forall n : nat,
  ∑ 0 n (fun k : nat => (n ∁ k) ^ 2) = (2 * n) ∁ n.
Proof.
  intros n. replace (2 * n)%nat with (n + n)%nat by lia. rewrite <- lemma_2_4_a with (m := n) (n := n).
  apply sum_f_equiv; try lia. intros k H1. rewrite n_choose_k_sym; try lia. lra.
Qed.