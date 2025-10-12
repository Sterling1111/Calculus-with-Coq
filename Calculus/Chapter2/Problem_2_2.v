From Lib Require Import Imports Sums.
Open Scope R_scope.

Lemma lemma_2_2_i : forall n : nat,
  (n >= 1)%nat -> ∑ 1 n (fun i => 2 * (INR i) - 1) = INR (n^2).
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
  (n >= 1)%nat -> ∑ 1 n (fun i => (2 * INR i - 1)^2) = INR n * (2 * INR n + 1) * (2 * INR n - 1) / 3.
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