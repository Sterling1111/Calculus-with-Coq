From Lib Require Import Imports Sums.
Open Scope R_scope.

Lemma lemma_2_1_i : forall n : nat,
  (n >= 1)%nat -> ∑ 1 n (fun i => INR i ^ 2) = (INR n * (INR n + 1) * (2 * INR n + 1)) / 6.
Proof.
  intros n H1. induction n as [| k IH]; try lia. assert (S k = 1 \/ k >= 1)%nat as [H2 | H2] by lia.
  - rewrite H2. compute. lra.
  - rewrite sum_f_i_Sn_f; try lia. rewrite IH; auto. rewrite S_INR. lra.
Qed.

Lemma lemma_2_1_ii : forall n : nat,
  (n >= 1)%nat -> ∑ 1 n (fun i => INR i ^ 3) = (sum_f 1 n (fun i => INR i)) ^ 2.
Proof.
  intros n H1. induction n as [| k IH]; try lia. assert (S k = 1 \/ k >= 1)%nat as [H2 | H2] by lia.
  - rewrite H2. compute. lra.
  - repeat rewrite sum_f_i_Sn_f; try lia. rewrite IH; auto. rewrite sum_n_nat; auto. repeat rewrite S_INR. lra.  
Qed.