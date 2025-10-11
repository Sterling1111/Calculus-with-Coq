Require Import Imports.
Open Scope R_scope.

Lemma Rpow_0 : forall k, 
  (k >= 1)%nat -> 0 ^ k = 0.
Proof.
  intros k H1. destruct k.
  - lia.
  - simpl. lra.
Qed.

Lemma Rpow_gt_0 : forall k r,
  r > 0 -> r ^ k > 0.
Proof.
  intros k r H1. induction k as [| k' IH].
  - simpl. lra.
  - simpl. nra.
Qed.

Lemma Rpow_equ_0 : forall n r,
  r ^ n = 0 -> r = 0.
Proof.
  intros n r. pose proof pow_nonzero r n.
  assert (H1 : r = 0 \/ r <> 0) by apply classic. destruct H1 as [H1 | H1].
  - intros H2. apply H1.
  - intros H2. apply H in H1. apply H1 in H2. exfalso. apply H2.
Qed.

Lemma Rpow_odd_lt_0 : forall x n,
  x < 0 -> (Nat.Odd n -> x^n < 0) /\ (Nat.Even n -> x^n > 0).
Proof.
  intros x n H1. induction n as [| k IH].
  - split.
    -- intro H2. destruct H2 as [k H2]. lia.
    -- intro H2. simpl. lra.
  - destruct IH as [IH1 IH2]. split.
    -- intro H2. simpl. rewrite Nat.Odd_succ in H2. apply IH2 in H2. nra.
    -- intro H2. simpl. rewrite Nat.Even_succ in H2. apply IH1 in H2. nra.
Qed.

Lemma Rpow_even_neg_eq_pos : forall x n,
  x < 0 -> (Nat.Even n -> (-x)^n = x^n) /\ (Nat.Odd n -> (-x)^n = -x^n).
Proof.
  intros x n H1. induction n as [| k IH].
  - simpl. split. reflexivity. intro H3. destruct H3 as [k H3]. lia.
  - simpl. destruct IH as [IH1 IH2]. split.
    -- intro H2. rewrite Nat.Even_succ in H2. rewrite IH2. lra. apply H2.
    -- intro H2. rewrite Nat.Odd_succ in H2. rewrite IH1. lra. apply H2.
Qed.

Lemma abs_smaller_neg_larger : forall x y, x < 0 -> y < 0 -> Rabs y < Rabs x -> x < y.
Proof.
  intros x y Hx Hy Habs.
  unfold Rabs in Habs.
  destruct (Rcase_abs x) as [Hx_neg | Hx_pos].
  - destruct (Rcase_abs y) as [Hy_neg | Hy_pos].
    -- lra.
    -- lra.
  - destruct (Rcase_abs y) as [Hy_neg | Hy_pos].
    -- lra.
    -- lra.
Qed.

Lemma lemma_1_6_a : forall x y n,
  0 <= x < y -> (0 < n)%nat -> x^n < y^n.
Proof.
  intros x y n [H1 H2] H3. induction n as [| k IH].
  - inversion H3.
  - simpl. destruct k as [| k'] eqn:Ek.
    -- simpl. repeat rewrite Rmult_1_r. apply H2.
    -- destruct H1 as [H1 | H1]. 2 : { apply Rmult_ge_0_gt_0_lt_compat. rewrite <- H1. simpl. lra. lra. lra. apply IH. lia. }
       { apply Rmult_gt_0_lt_compat. apply Rpow_gt_0. lra. lra. lra. apply IH. lia. }
Qed.

Lemma lemma_1_6_b : forall x y n,
  x < y -> Nat.Odd n -> x^n < y^n.
Proof.
  intros x y n H1 H2. assert (H3 : x >= 0 \/ x < 0) by lra. destruct H3 as [H3 | H3].
  - apply lemma_1_6_a. split. lra. lra. destruct H2 as [k H2]. lia.
  - pose proof H3 as H3'. apply Rpow_odd_lt_0 with (n := n) in H3. destruct H3 as [H3 H4]. pose proof H2 as H2'.
    apply H3 in H2. assert (H5 : y > 0 \/ y = 0 \/ y < 0) by lra. destruct H5 as [H5 | [H5 | H5]].
    -- assert (H6 : y ^ n > 0). { apply Rpow_gt_0. lra. } nra.
    -- rewrite H5. assert (H6 : (n = 0 \/ n >= 1)%nat) by lia. destruct H6 as [H6 | H6].    
       --- rewrite H6 at 2. simpl. lra.
       --- apply Rpow_0 in H6. rewrite H6. lra.
    -- assert (H6 : (-y)^n < (-x)^n). { apply lemma_1_6_a. split. lra. lra. destruct H2' as [k H2']. lia. }
       assert (H7 : (y)^n < 0). { apply Rpow_odd_lt_0. lra. apply H2'. } replace (-x) with (Rabs x) in H6. 2 : { apply Rabs_left. apply H3'. }
       replace (-y) with (Rabs y) in H6. 2 : { apply Rabs_left. apply H5. } repeat rewrite RPow_abs in H6. 
       apply abs_smaller_neg_larger; assumption.
Qed.

Lemma lemma_1_6_c : forall x y n,
  x ^ n = y ^ n -> Nat.Odd n -> x = y.
Proof.
  intros x y n H1 H2. pose proof Rtotal_order x y as H3. destruct H3 as [H3 | [H3 | H3]].
  - pose proof lemma_1_6_b x y n as H4. apply H4 in H3. 2 : { apply H2. } lra.
  - apply H3.
  - pose proof lemma_1_6_b y x n as H4. apply H4 in H3. 2 : { apply H2. } lra.
Qed.

Lemma lemma_1_6_d : forall x y n,
  x ^ n = y ^ n -> Nat.Even n -> (0 < n)%nat -> (x = y \/ x = -y).
Proof.
  intros x y n H1 H2 H3. 
  assert (H4 : (x >= 0 /\ y >= 0) \/ (x < 0 /\ y < 0) \/ (x >= 0 /\ y < 0) \/ (x < 0 /\ y >= 0)) by lra. 
  destruct H4 as [H4 | [H4 | [H4 | H4]]].
  - destruct H4 as [H4 H5]. pose proof Rtotal_order x y as H6. destruct H6 as [H6 | [H6 | H6]].
    -- pose proof lemma_1_6_a x y n as H7. assert (H8 : 0 <= x < y) by lra. apply H7 in H8. 2 : { apply H3. } lra.
    -- left. apply H6.
    -- pose proof lemma_1_6_a y x n as H7. assert (H8 : 0 <= y < x) by lra. apply H7 in H8. 2 : { apply H3. } lra.
  - destruct H4 as [H4 H5]. pose proof Rtotal_order x y as H6. destruct H6 as [H6 | [H6 | H6]].
    -- assert (H7 : -x > 0 /\ -y > 0 /\ -x > -y) by lra. destruct H7 as [H7 [H8 H9]]. pose proof lemma_1_6_a (-y) (-x) n as H10.
       assert (H11 : 0 <= -y < -x) by lra. apply H10 in H11. 2 : { apply H3. }  pose proof Rpow_even_neg_eq_pos (x) n as H12.
       destruct H12 as [H12 H13]. apply H4. pose proof H2 as H2'. apply H12 in H2. rewrite <- H2 in H1. pose proof Rpow_even_neg_eq_pos (y) n as H14.
       destruct H14 as [H14 H15]. apply H5. apply H14 in H2'. rewrite <- H2' in H1. lra.
    -- left. apply H6.
    -- assert (H7 : -x > 0 /\ -y > 0 /\ -x < -y) by lra. destruct H7 as [H7 [H8 H9]]. pose proof lemma_1_6_a (-x) (-y) n as H10.
       assert (H11 : 0 <= -x < -y) by lra. apply H10 in H11. 2 : { apply H3. }  pose proof Rpow_even_neg_eq_pos (y) n as H12.
       destruct H12 as [H12 H13]. apply H5. pose proof H2 as H2'. apply H12 in H2. rewrite <- H2 in H1. pose proof Rpow_even_neg_eq_pos (x) n as H14.
       destruct H14 as [H14 H15]. apply H4. apply H14 in H2'. rewrite <- H2' in H1. lra.
  - destruct H4 as [H4 H5]. pose proof Rtotal_order x y as H6. destruct H6 as [H6 | [H6 | H6]].
    -- pose proof lemma_1_6_a x y n as H7. assert (H8 : 0 <= x < y) by lra. apply H7 in H8. 2 : { apply H3. } lra.
    -- left. apply H6.
    -- right. pose proof Rtotal_order x (-y) as H7. destruct H7 as [H7 | [H7 | H7]].
       --- pose proof lemma_1_6_a x (-y) n as H8. assert (H9 : 0 <= x < -y) by lra. apply H8 in H9. 2 : { apply H3. } 
           assert (H10 : (-y)^n = y^n). { pose proof Rpow_even_neg_eq_pos y n as H10. destruct H10 as [H10 H11]. apply H5. apply H10. apply H2. } lra.
       --- apply H7.
       --- pose proof lemma_1_6_a (-y) x n as H8. assert (H9 : 0 <= -y < x) by lra. apply H8 in H9. 2 : { apply H3. } 
           assert (H10 : (-y)^n = y^n). { pose proof Rpow_even_neg_eq_pos y n as H10. destruct H10 as [H10 H11]. apply H5. apply H10. apply H2. } lra.
- destruct H4 as [H4 H5]. pose proof Rtotal_order y x as H6. destruct H6 as [H6 | [H6 | H6]].
    -- pose proof lemma_1_6_a y x n as H7. assert (H8 : 0 <= y < x) by lra. apply H7 in H8. 2 : { apply H3. } lra.
    -- left. auto.
    -- right. pose proof Rtotal_order y (-x) as H7. destruct H7 as [H7 | [H7 | H7]].
       --- pose proof lemma_1_6_a y (-x) n as H8. assert (H9 : 0 <= y < -x) by lra. apply H8 in H9. 2 : { apply H3. } 
           assert (H10 : (-x)^n = x^n). { pose proof Rpow_even_neg_eq_pos x n as H10. destruct H10 as [H10 H11]. apply H4. apply H10. apply H2. } lra.
       --- lra.
       --- pose proof lemma_1_6_a (-x) y n as H8. assert (H9 : 0 <= -x < y) by lra. apply H8 in H9. 2 : { apply H3. } 
           assert (H10 : (-x)^n = x^n). { pose proof Rpow_even_neg_eq_pos x n as H10. destruct H10 as [H10 H11]. apply H4. apply H10. apply H2. } lra.
Qed.