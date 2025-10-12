From Lib Require Import Imports.
Open Scope R_scope.

Definition one_and_only_one_3 (P1 P2 P3 : Prop) : Prop :=
  (P1 /\ ~ P2 /\ ~ P3) \/ (~ P1 /\ P2 /\ ~ P3) \/ (~ P1 /\ ~ P2 /\ P3).

Definition P10' := forall a b : R, one_and_only_one_3 (a = b) (a < b) (b < a). 
Definition P11' := forall a b c : R, (a < b /\ b < c) -> a < c.
Definition P12' := forall a b c : R, a < b -> a + c < b + c.
Definition P13' := forall a b c : R, a < b /\ 0 < c -> a * c < b * c.

Definition P10 := forall (P : R -> Prop) (a : R),
  (forall r : R, P r <-> 0 < r) -> one_and_only_one_3 (a = 0) (P a) (P (-a)).

Definition P11 := forall (P : R -> Prop) (a b : R),
  (forall r : R, P r <-> 0 < r) -> (P a /\ P b) -> P (a + b).

Definition P12 := forall (P : R -> Prop) (a b : R),
  (forall r : R, P r <-> 0 < r) -> (P a /\ P b) -> P (a * b).

Theorem Rplus_neg_neg : P11' -> P12' -> forall a b : R, a < 0 -> b < 0 -> a + b < 0.
Proof.
  intros H1 H2 a b H3 H4. unfold P11', P12' in H1, H2. specialize H2 with (a := a) (b := 0) (c := b).
  rewrite Rplus_0_l in H2. apply H2 in H3. apply H1 with (a := a + b) (b := b) (c := 0).
  split. apply H3. apply H4.
Qed.

Theorem Rplus_pos_pos : P11' -> P12' -> forall a b : R, a > 0 -> b > 0 -> a + b > 0.
Proof.
  intros H1 H2 a b H3 H4. unfold P11', P12' in H1, H2. specialize H2 with (a := 0) (b := a) (c := b).
  rewrite Rplus_0_l in H2. apply H2 in H3. apply Rlt_gt. apply H1 with (a := 0) (b := b) (c := a + b).
  split. apply Rgt_lt. apply H4. apply H3.
Qed.

Lemma Ropp_gt_lt_0_contravar' : P10' -> P11' -> P12' -> forall a, a < 0 <-> -a > 0.
Proof.
  intros H1 H11 H12 a. split.
  {
    intros H2.
    unfold P10' in H1. pose proof H1 as H1'. specialize H1 with (a := a + (-a)) (b := 0).
    unfold one_and_only_one_3 in H1. destruct H1 as [[H3 [H4 H5]] | [[H3 [H4 H5]] | [H3 [H4 H5]]]].
    - unfold not in *. assert (H6 : (-a < 0 -> False) /\ (-a = 0 -> False)). 
      -- split.
        --- intro H6. apply H4. apply Rplus_neg_neg; assumption.
        --- intro H6. apply H4. rewrite H6. rewrite Rplus_0_r. apply H2.
      -- destruct H6 as [H6 H7]. specialize H1' with (a := -a) (b := 0). unfold one_and_only_one_3 in H1'.
        destruct H1' as [[H8 [H9 H10]] | [[H8 [H9 H10]] | [H8 [H9 H10]]]].
        --- unfold not in *. apply H7 in H8. exfalso. apply H8.
        --- apply H6 in H9. exfalso. apply H9.
        --- apply H10.
    - exfalso. rewrite Rplus_opp_r in H3. unfold not in H3. assert (H6 : 0 = 0) by reflexivity. apply H3 in H6. apply H6.
    - exfalso. rewrite Rplus_opp_r in H3. unfold not in H3. assert (H6 : 0 = 0) by reflexivity. apply H3 in H6. apply H6.
  }
  {
    intros H2.
    unfold P10' in H1. pose proof H1 as H1'. specialize H1 with (a := a + (-a)) (b := 0).
    unfold one_and_only_one_3 in H1. destruct H1 as [[H3 [H4 H5]] | [[H3 [H4 H5]] | [H3 [H4 H5]]]].
    - unfold not in *. assert (H6 : (a > 0 -> False) /\ (a = 0 -> False)). 
      -- split.
        --- intros H6. apply H5. apply Rplus_pos_pos; assumption.
        --- intros H6. apply H5. rewrite H6 at 1. rewrite Rplus_0_l. apply Rgt_lt. apply H2.
      -- destruct H6 as [H6 H7]. specialize H1' with (a := a) (b := 0). unfold one_and_only_one_3 in H1'.
        destruct H1' as [[H8 [H9 H10]] | [[H8 [H9 H10]] | [H8 [H9 H10]]]].
        --- unfold not in *. apply H7 in H8. exfalso. apply H8.
        --- apply H9.
        --- exfalso. apply H6 in H10. apply H10.
    - exfalso. rewrite Rplus_opp_r in H3. unfold not in H3. assert (H6 : 0 = 0) by reflexivity. apply H3 in H6. apply H6.
    - exfalso. rewrite Rplus_opp_r in H3. unfold not in H3. assert (H6 : 0 = 0) by reflexivity. apply H3 in H6. apply H6.
  } 
Qed.

Lemma lemma_1_8_P10 : P10' -> P11' -> P12' -> P10.
Proof.
  intros H1 H11 H12. unfold P10. intros P a. pose proof H1 as H1'. unfold P10' in H1. intros H2.
  unfold one_and_only_one_3 in *. specialize H1 with (a := a) (b := 0).
  destruct H1 as [[H1 [H3 H4]] | [[H1 [H3 H4]] | [H1 [H3 H4]]]].
  - left. split.
    -- apply H1.
    -- split.
      --- unfold not. intro H5. specialize H2 with (r := a). apply H2 in H5. unfold not in H4. apply H4 in H5. apply H5.
      --- unfold not. intro H5. specialize H2 with (r := -a). apply H2 in H5. unfold not in H3. apply Rlt_gt in H5. 
          apply Ropp_gt_lt_0_contravar' in H5; try apply H3; assumption.
  - right. right. split.
    -- apply H1.
    -- split.
      --- specialize H2 with (r := a). unfold not in *. intro H5. apply H2 in H5. apply H4 in H5. apply H5.
      --- specialize H2 with (r := -a). apply Ropp_gt_lt_0_contravar' in H3; try apply H2; assumption.
  - right. left. split.
    -- apply H1.
    -- split.
      --- specialize H2 with (r := a). apply H2 in H4. apply H4.
      --- specialize H2 with (r := -a). unfold not in *. intro H5. apply H2 in H5. apply Ropp_gt_lt_0_contravar' in H5; try apply H3; assumption. 
Qed.

Lemma lemma_1_8_P11 : (P11' /\ P12') -> P11.
Proof.
  intros [H1 H2]. unfold P11. intros P a b H3 [H4 H5].
  unfold P11', P12' in H1, H2. apply H3 in H4. apply H3 in H5.
  assert (H6 : forall r1 r2 r3 r4, r1 < r2 /\ r3 < r4 -> r1 + r3 < r2 + r3 < r2 + r4).
  - intros r1 r2 r3 r4 [H6 H7]. split.
    -- apply H2. apply H6.
    -- rewrite Rplus_comm. rewrite Rplus_comm with (r1 := r2). apply H2. apply H7.
  - specialize (H6 0 a 0 b). destruct H6 as [H6 H7]. (split; try apply H4; apply H5).
    specialize (H1 (0 + 0) (a + 0) (a + b)). rewrite Rplus_0_l in*.
    assert (H8 : 0 < a + b). { apply H1. split. apply H6. apply H7. }
    apply H3. apply H8.
Qed.

Lemma lemma_1_8_P12 : P13' -> P12.
Proof.
  intros H1. unfold P13', P12 in *. intros P a b H2 [H3 H4].
  apply H2 in H3. apply H2 in H4. specialize H1 with (a := 0) (b := a) (c := b).
  assert (H5 : 0 < a /\ 0 < b) by (split; assumption). apply H1 in H5. 
  rewrite Rmult_0_l in H5. apply H2 in H5. apply H5.
Qed.