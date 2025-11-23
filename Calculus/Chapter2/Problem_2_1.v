From Calculus.Chapter2 Require Import Prelude.

Lemma lemma_2_1_i : ∀ n,
  (n >= 1)%nat -> ∑ 1 n (λ i, i ^ 2) = (n * (n + 1) * (2 * n + 1)) / 6.
Proof.
  intros n H1. induction n as [| k IH]; try lia. assert (k = 0 \/ k >= 1)%nat as [H2 | H2] by lia.
  - rewrite H2, sum_f_n_n. simpl. field_simplify. reflexivity.
  - rewrite sum_f_i_Sn_f; try lia. rewrite IH; auto. rewrite S_INR. lra.
Qed.

Lemma lemma_2_1_ii : ∀ n,
  (n >= 1)%nat -> ∑ 1 n (λ i, i^3) = (∑ 1 n (λ i, i)) ^ 2.
Proof.
  intros n H1. induction n as [| k IH]; try lia. assert (S k = 1 \/ k >= 1)%nat as [H2 | H2] by lia.
  - rewrite H2. compute. lra.
  - repeat rewrite sum_f_i_Sn_f; try lia. rewrite IH; auto. rewrite sum_n_nat; auto. repeat rewrite S_INR. lra.  
Qed.