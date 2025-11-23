From Calculus.Chapter2 Require Import Prelude Problem_2_1.

Lemma lemma_2_6_i : ∀ n,
  (n >= 1)%nat -> ∑ 1 n (λ i, i^3) = n^4 / 4 + n^3 / 2 + n^2 / 4.
Proof.
  intros n H1.
  assert (H2 : ∀ r, (r + 1)^4 - r^4 = 4 * r^3 + 6 * r^2 + 4 * r + 1) by (intros; nra).
  assert (H3 : ∑ 1 n (fun k => (k + 1)^4 - k^4) = (n+1)^4 - 1).
  {
    set (f := fun x : nat => x ^ 4). replace ((n + 1)^4) with (f (n+1)%nat) by (unfold f; solve_R).
    replace (f (n + 1)%nat - 1) with (f (n + 1)%nat - f 1%nat)  by (compute; lra).
    pose proof sum_f_1_n_fSi_minus_fi n f H1 as H3. unfold f in *.
    rewrite <- H3. apply sum_f_equiv; auto. intros k H4. solve_R.
  }
  assert (H4 : ∑ 1 n (λ k, 4 * k^3 + 6 * k^2 + 4 * k + 1) = 4 * (∑ 1 n (λ k, k^3)) + 6 * (∑ 1 n (λ k, k^2)) + 4 * (∑ 1 n (λ k, k)) + (∑ 1 n (λ k, 1))).
  {
    clear H3.
    induction n as [| n' IH]; try lia. assert (S n' = 1 \/ n' >= 1)%nat as [H3 | H3] by lia.
    - rewrite H3. compute. nra.
    - repeat rewrite sum_f_i_Sn_f; try lia. rewrite IH; auto. repeat rewrite S_INR. simpl. nra.
  }
  rewrite sum_n_nat in H4; auto. rewrite lemma_2_1_i in H4; auto.
  assert (H5 : (λ k : nat, (k + 1)^4 - k^4) = (λ k : nat, 4 * k^3 + 6 * k^2 + 4 * k + 1)).
  { apply functional_extensionality. intros x. lra. } 
  replace (∑ 1 n λ _ : nat, 1) with (INR n) in H4. 2 : { rewrite sum_f_const. break_INR; auto. solve_INR. }

  rewrite <- H5 in H4. rewrite H3 in H4. replace (∑ 1 n (λ i, i^3)) with
  (((n + 1) ^ 4 - 1 - 6 * (n * (n + 1) * (2 * n + 1) / 6) - 4 * (n * (n + 1) / 2) - n) / 4); nra.
Qed.

Lemma lemma_2_6_ii : forall n,
  (n >= 1)%nat -> ∑ 1 n (λ i, i^4) = n^5 / 5 + n^4 / 2 + n^3 / 3 - n / 30.
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
  (n >= 1)%nat -> ∑ 1 n (fun i => 1 / INR (i * (i + 1))) = 1 - 1 / INR (n + 1).
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