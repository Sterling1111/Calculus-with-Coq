From Lib Require Import Imports Sets Notations Functions.
Import SetNotations.

Open Scope R_scope.

Definition is_lower_bound (E:Ensemble ℝ) lb := forall x, x ∈ E -> x >= lb.
Definition is_upper_bound (E:Ensemble ℝ) ub := forall x, x ∈ E -> x <= ub.

Definition has_lower_bound (E:Ensemble ℝ) := exists lb, is_lower_bound E lb.
Definition has_upper_bound (E:Ensemble ℝ) := exists ub, is_upper_bound E ub.

Definition is_glb (E:Ensemble ℝ) glb :=
  is_lower_bound E glb /\ (forall lb, is_lower_bound E lb -> glb >= lb).

Definition is_lub (E:Ensemble ℝ) lub :=
  is_upper_bound E lub /\ (forall ub, is_upper_bound E ub -> lub <= ub).

Lemma completeness_upper_bound : forall E:Ensemble ℝ,
  has_upper_bound E -> E ≠ ∅ -> { sup | is_lub E sup }.
Proof.
  intros E H1 H2. apply not_Empty_In in H2. assert (H3 : bound E).
  { destruct H1 as [ub H1]. exists ub. intros x H3. apply H1. apply H3. }
  apply completeness; auto.
Qed.

Lemma completeness_lower_bound :
    forall E:Ensemble ℝ, has_lower_bound E -> E ≠ ∅ -> { inf | is_glb E inf }.
Proof.
  intros E H1 H2. set (E' := fun x => -x ∈ E). assert (H3 : forall x, x ∈ E <-> -x ∈ E').
  {
    intros x. split; intros H3.
    - unfold Ensembles.In, E' in *. rewrite Ropp_involutive. apply H3.
    - unfold Ensembles.In, E' in *. rewrite Ropp_involutive in H3. apply H3.
  }
  assert (H4 : has_upper_bound E').
  { destruct H1 as [lb H1]. exists (-lb). intros x H4. specialize (H1 (-x) H4). lra. }
  assert (H5 : E' ≠ ∅).
  { apply not_Empty_In in H2 as [x H2]. apply not_Empty_In. exists (-x). apply H3 in H2; auto. }
  destruct (completeness_upper_bound E' H4 H5) as [lub H6]. exists (-lub). split.
  - intros x H7. destruct H6 as [H6 _]. specialize (H6 (-x)). apply H3 in H7. specialize (H6 H7). lra.
  - intros lb H7. destruct H6 as [_ H6]. specialize (H6 (-lb)). replace (-lub >= lb) with (lub <= -lb).
    2 : { apply propositional_extensionality. lra. } apply H6. intros x H8. specialize (H7 (-x)). specialize (H3 (-x)).
    rewrite Ropp_involutive in H3. apply H3 in H8. specialize (H7 H8). lra.
Qed.

Lemma lub_unique : forall (E:Ensemble ℝ) a b, is_lub E a -> is_lub E b -> a = b.
Proof.
  intros E a b [H1 H2] [H3 H4]. specialize (H4 a H1). specialize (H2 b H3). lra.
Qed.

Lemma glb_unique : forall (E:Ensemble ℝ) a b, is_glb E a -> is_glb E b -> a = b.
Proof.
  intros E a b [H1 H2] [H3 H4]. specialize (H4 a H1). specialize (H2 b H3). lra.
Qed.

Lemma lub_ge_all_In : forall E a x, is_lub E a -> x ∈ E -> x <= a.
Proof.
  intros E a x [H1 H2] H3. specialize (H1 x H3). lra.
Qed.

Lemma lub_lt_not_In : forall E a x, is_lub E a -> x > a -> x ∉ E.
Proof.
  intros E a x H1 H2 H3. pose proof lub_ge_all_In E a x H1 H3 as H4. lra.
Qed.

Lemma glb_le_all_In : forall E a x, is_glb E a -> x ∈ E -> a <= x.
Proof.
  intros E a x [H1 H2] H3. specialize (H1 x H3). lra.
Qed.

Lemma glb_gt_not_In : forall E a x, is_glb E a -> x < a -> x ∉ E.
Proof.
  intros E a x H1 H2 H3. pose proof glb_le_all_In E a x H1 H3 as H4. lra.
Qed.

Lemma exists_lub_set_not_empty : forall (E:Ensemble ℝ) (a:R), is_lub E a -> E ≠ ∅.
Proof.
  intros E a [H1 H2]. intros H3. assert (H4 : is_upper_bound E (a-1)).
  { intros x H4. specialize (H1 x H4). autoset. }
  specialize (H2 (a-1) H4). lra.
Qed.

Lemma exists_glb_set_not_empty : forall (E:Ensemble ℝ) (a:R), is_glb E a -> E ≠ ∅.
Proof.
  intros E a [H1 H2]. intros H3. assert (H4 : is_lower_bound E (a+1)).
  { intros x H4. specialize (H1 x H4). autoset. }
  specialize (H2 (a+1) H4). lra.
Qed.

Lemma lub_eq_glb_diff_lt_eps : forall (E1 E2 : Ensemble ℝ) (a ε : ℝ),
  is_lub E1 a -> is_glb E2 a -> ε > 0 -> exists x1 x2, x1 ∈ E1 /\ x2 ∈ E2 /\ x2 - x1 < ε.
Proof.
  intros E1 E2 a ε H1 H2 H3. pose proof classic (a ∈ E1) as [H4 | H4]; pose proof classic (a ∈ E2) as [H5 | H5].
  - exists a, a. repeat split; auto. lra.
  - pose proof classic (forall x, 0 < x < ε -> (x + a) ∉ E2) as [H6 | H6].
    -- assert (is_lower_bound E2 (a + ε)) as H7.
       {
         intros x H7. assert (x >= a + ε \/ x < a + ε) as [H8 | H8] by lra; auto. pose proof Rtotal_order x a as [H9 | [H9 | H9]].
         - pose proof glb_le_all_In E2 a x H2 H7 as H10. lra.
         - subst. tauto.
         - specialize (H6 (x - a) ltac:(lra)). replace (x - a + a) with x in H6 by lra. tauto.
       }
       destruct H2 as [_ H2]. specialize (H2 (a + ε) H7). lra.
    -- apply not_all_ex_not in H6 as [x H6]. apply imply_to_and in H6 as [H6 H7]. assert ((x + a) ∈ E2) as H8 by tauto.
       exists a, (x + a). repeat split; auto. lra.
  - pose proof classic (forall x, 0 < x < ε -> (a - x) ∉ E1) as [H6 | H6].
    -- assert (is_upper_bound E1 (a - ε)) as H7.
       {
         intros x H7. assert (x <= a - ε \/ x > a - ε) as [H8 | H8] by lra; auto. pose proof Rtotal_order x a as [H9 | [H9 | H9]].
         - specialize (H6 (a - x) ltac:(lra)). replace (a - (a - x)) with x in H6 by lra. tauto.
         - subst. tauto.
         - pose proof lub_ge_all_In E1 a x H1 H7 as H10. assert (x = a) as H11 by lra. subst. tauto.
       }
       destruct H1 as [_ H1]. specialize (H1 (a - ε) H7). lra.
    -- apply not_all_ex_not in H6 as [x H6]. apply imply_to_and in H6 as [H6 H7]. assert ((a - x) ∈ E1) as H8 by tauto.
       exists (a - x), a. repeat split; auto. lra.
  - pose proof classic (forall x, 0 < x < ε/2 -> (a - x) ∉ E1) as [H6 | H6]; pose proof classic (forall x, 0 < x < ε/2 -> (x + a) ∉ E2) as [H7 | H7].
    -- assert (is_upper_bound E1 (a - ε/2)) as H8.
       {
         intros x H8. assert (x <= a - ε/2 \/ x > a - ε/2) as [H9 | H9] by lra; auto. pose proof Rtotal_order x a as [H10 | [H10 | H10]].
         - specialize (H6 (a - x) ltac:(lra)). replace (a - (a - x)) with x in H6 by lra. tauto.
         - subst. tauto.
         - pose proof lub_ge_all_In E1 a x H1 H8 as H11. assert (x = a) as H12 by lra. subst. tauto.
       }
       destruct H1 as [_ H1]. specialize (H1 (a - ε/2) H8) as H9. lra.
    -- assert (is_upper_bound E1 (a - ε/2)) as H8.
       {
         intros x H8. assert (x <= a - ε/2 \/ x > a - ε/2) as [H9 | H9] by lra; auto. pose proof Rtotal_order x a as [H10 | [H10 | H10]].
         - specialize (H6 (a - x) ltac:(lra)). replace (a - (a - x)) with x in H6 by lra. tauto.
         - subst. tauto.
         - pose proof lub_ge_all_In E1 a x H1 H8 as H11. assert (x = a) as H12 by lra. subst. tauto.
       }
       destruct H1 as [_ H1]. specialize (H1 (a - ε/2) H8) as H9. lra.
    -- assert (is_lower_bound E2 (a + ε/2)) as H8.
       {
         intros x H8. assert (x >= a + ε/2 \/ x < a + ε/2) as [H9 | H9] by lra; auto. pose proof Rtotal_order x a as [H10 | [H10 | H10]].
         - pose proof glb_le_all_In E2 a x H2 H8 as H11. lra.
         - subst. tauto.
         - specialize (H7 (x - a) ltac:(lra)). replace (x - a + a) with x in H7 by lra. tauto.
       }
       destruct H2 as [_ H2]. specialize (H2 (a + ε/2) H8) as H9. lra.
    -- apply not_all_ex_not in H6 as [x H6]. apply imply_to_and in H6 as [H6 H10]. assert ((a - x) ∈ E1) as H11 by tauto.
       apply not_all_ex_not in H7 as [y H7]. apply imply_to_and in H7 as [H7 H12]. assert ((y + a) ∈ E2) as H13 by tauto.
       exists (a - x), (y + a). repeat split; auto. lra.
Qed.

Lemma inf_le_sup : forall (E : Ensemble ℝ) a b, is_glb E a -> is_lub E b -> a <= b.
Proof.
  intros E a b H1 H2. pose proof exists_lub_set_not_empty E b H2 as H3. assert (exists x, x ∈ E) as [x H4].
  { apply not_Empty_In in H3. auto. }
  pose proof glb_le_all_In E a x H1 H4 as H5.
  pose proof lub_ge_all_In E b x H2 H4 as H6. lra.
Qed.

Lemma sup_le_inf : forall (E1 E2 : Ensemble ℝ) a b, is_lub E1 a -> is_glb E2 b ->
  (forall x y, x ∈ E1 -> y ∈ E2 -> x <= y) -> a <= b.
Proof.
  intros E1 E2 a b H1 H2 H3. assert (a <= b \/ a > b) as [H4 | H4]; try lra.
  pose proof classic (a ∈ E1) as [H5 | H5]; pose proof classic (b ∈ E2) as [H6 | H6].
  - specialize (H3 a b H5 H6). lra.
  - pose proof classic (forall x, 0 < x < a - b -> (b + x) ∉ E2) as [H7 | H7].
    -- assert (is_lower_bound E2 a) as H8.
       {
         intros x H8. assert (x >= a \/ x < a) as [H9 | H9] by lra; auto. pose proof Rtotal_order x b as [H10 | [H10 | H10]].
         - pose proof glb_le_all_In E2 b x H2 H8 as H11. lra.
         - subst. tauto.
         - specialize (H7 (x - b) ltac:(lra)). replace (b + (x - b)) with x in H7 by lra. tauto.
       }
       destruct H2 as [_ H2]. specialize (H2 a H8). lra.
    -- apply not_all_ex_not in H7 as [x H7]. apply imply_to_and in H7 as [H7 H8]. assert ((b + x) ∈ E2) as H9 by tauto.
       specialize (H3 a (b + x) H5 H9). lra.
  - pose proof classic (forall x, 0 < x < a - b -> (a - x) ∉ E1) as [H7 | H7].
    -- assert (is_upper_bound E1 b) as H8.
       { intros x H8. assert (x <= b \/ x > b) as [H9 | H9] by lra; auto. }
       destruct H1 as [_ H1]. specialize (H1 b H8). lra.
    -- apply not_all_ex_not in H7 as [x H7]. apply imply_to_and in H7 as [H7 H8]. assert ((a - x) ∈ E1) as H9 by tauto.
       specialize (H3 (a - x) b H9 H6). lra.
  - pose proof classic (forall x, 0 < x < (a - b)/2 -> (a - x) ∉ E1) as [H7 | H7]; pose proof classic (forall x, 0 < x < (a - b)/2 -> (b + x) ∉ E2) as [H8 | H8].
    -- assert (is_upper_bound E1 ((a + b) / 2)) as H9.
       {
          intros x H9. assert (x <= (a + b) / 2 \/ x > (a + b) / 2) as [H10 | H10] by lra; auto. pose proof Rtotal_order x a as [H11 | [H11 | H11]].
          - specialize (H7 (a - x) ltac:(lra)). replace (a - (a - x)) with x in H7 by lra. tauto.
          - subst. tauto.
          - pose proof lub_ge_all_In E1 a x H1 H9 as H12. lra.
       }
       destruct H1 as [_ H1]. specialize (H1 ((a + b) / 2) H9). lra.
    -- assert (is_upper_bound E1 ((a + b) / 2)) as H9.
       {
          intros x H9. assert (x <= (a + b) / 2 \/ x > (a + b) / 2) as [H10 | H10] by lra; auto. pose proof Rtotal_order x a as [H11 | [H11 | H11]].
          - specialize (H7 (a - x) ltac:(lra)). replace (a - (a - x)) with x in H7 by lra. tauto.
          - subst. tauto.
          - pose proof lub_ge_all_In E1 a x H1 H9 as H12. lra.
       }
       destruct H1 as [_ H1]. specialize (H1 ((a + b) / 2) H9). lra.
    -- assert (is_lower_bound E2 ((a + b) / 2)) as H9.
       {
          intros x H9. assert (x >= (a + b) / 2 \/ x < (a + b) / 2) as [H10 | H10] by lra; auto. pose proof Rtotal_order x b as [H11 | [H11 | H11]].
          - pose proof glb_le_all_In E2 b x H2 H9 as H12. lra.
          - subst. tauto.
          - specialize (H8 (x - b) ltac:(lra)). replace (b + (x - b)) with x in H8 by lra. tauto.
       }
       destruct H2 as [_ H2]. specialize (H2 ((a + b) / 2) H9). lra.
    -- apply not_all_ex_not in H7 as [x H7]. apply imply_to_and in H7 as [H7 H9]. assert ((a - x) ∈ E1) as H10 by tauto.
       apply not_all_ex_not in H8 as [y H8]. apply imply_to_and in H8 as [H8 H11]. assert ((b + y) ∈ E2) as H12 by tauto.
       specialize (H3 (a - x) (b + y) H10 H12). lra.
Qed.

Lemma exists_point_within_delta : forall A a δ, is_lub A a -> δ > 0 -> exists x, x ∈ A /\ a - δ < x <= a.
Proof.
  intros A a δ H1 H2. pose proof classic (a ∈ A) as [H3 | H3].
  - exists a. repeat split; try lra; auto.
  - pose proof classic (∃ x, x ∈ A /\ a - δ < x <= a) as [H4 | H4]; auto.
    exfalso. apply H3. assert (H5 : forall x, x ∈ A -> a - δ >= x).
    {
      intros x H5. pose proof classic (a - δ >= x) as [H6 | H6]; auto. exfalso. apply H4. exists x. repeat split; auto; try lra.
      apply lub_ge_all_In with (E := A); auto.
    }
    assert (H6 : is_upper_bound A (a - (δ/2))).
    {
      intros x H6. specialize (H5 x H6). lra.
    }
    destruct H1 as [_ H1]. specialize (H1 (a - δ/2) H6). lra.
Qed.

Lemma glb_subset : forall (E1 E2 : Ensemble ℝ) r1 r2,
  is_glb E1 r1 -> is_glb E2 r2 -> E1 ⊆ E2 -> r2 <= r1.
Proof.
  intros E1 E2 r1 r2 H1 H2 H3. unfold is_glb in H1, H2. destruct H1 as [H1 H4], H2 as [H2 H5].
  specialize (H4 r2). apply Rge_le. apply H4. intros x H6. specialize (H3 x H6). specialize (H2 x). apply H2. auto.
Qed.

Lemma lub_subset : forall (E1 E2 : Ensemble ℝ) r1 r2,
  is_lub E1 r1 -> is_lub E2 r2 -> E1 ⊆ E2 -> r1 <= r2.
Proof.
  intros E1 E2 r1 r2 H1 H2 H3. unfold is_lub in H1, H2. destruct H1 as [H1 H4], H2 as [H2 H5].
  specialize (H4 r2). apply H4. intros x H6. specialize (H3 x H6). specialize (H2 x). apply H2. auto.
Qed.

Lemma is_glb_mult_pos : forall E c m x0,
  0 <= c -> E x0 -> is_glb E m -> is_glb (fun y => exists x, E x /\ y = c * x) (c * m).
Proof.
  intros E c m x0 H1 H2 [H3 H4]. split.
  - intros y [x [H5 H6]]. subst y. specialize (H3 x H5). nra.
  - intros b H5. destruct (Rle_lt_dec c 0) as [H6|H6].
    + assert (c = 0) by lra. subst c. assert (b <= 0). { apply Rge_le, H5. exists x0; split; auto; lra. } lra.
    + assert (is_lower_bound E (b / c)) as H7.
      { intros x H8. assert (H9 : b <= c * x). { apply Rge_le, H5. exists x; split; auto; lra. }
        apply Rmult_le_compat_l with (r := / c) in H9; [|apply Rlt_le, Rinv_0_lt_compat; lra].
        replace (/ c * (c * x)) with x in H9 by (field; lra).
        replace (/ c * b) with (b / c) in H9 by (field; lra). lra. }
      specialize (H4 _ H7). apply Rmult_ge_compat_l with (r := c) in H4; try lra.
      replace (c * (b / c)) with b in H4 by (field; lra). auto.
Qed.

Lemma is_lub_mult_pos : forall E c m x0,
  0 <= c -> E x0 -> is_lub E m -> is_lub (fun y => exists x, E x /\ y = c * x) (c * m).
Proof.
  intros E c m x0 H1 H2 [H3 H4]. split.
  - intros y [x [H5 H6]]. subst y. specialize (H3 x H5). apply Rmult_le_compat_l; lra.
  - intros b H5. destruct (Rle_lt_dec c 0) as [H6|H6].
    + assert (c = 0) by lra. subst c. assert (0 <= b). { apply H5. exists x0; split; auto; lra. } lra.
    + assert (is_upper_bound E (b / c)) as H7.
      { intros x H8. assert (H9 : c * x <= b). { apply H5. exists x; split; auto; lra. }
        apply Rmult_le_compat_l with (r := / c) in H9; [|apply Rlt_le, Rinv_0_lt_compat; lra].
        replace (/ c * (c * x)) with x in H9 by (field; lra).
        replace (/ c * b) with (b / c) in H9 by (field; lra). auto. }
      specialize (H4 _ H7). apply Rmult_le_compat_l with (r := c) in H4; [|lra].
      replace (c * (b / c)) with b in H4 by (field; lra). auto.
Qed.

Lemma is_glb_mult_neg : forall E c m x0,
  c <= 0 -> E x0 -> is_lub E m -> is_glb (fun y => exists x, E x /\ y = c * x) (c * m).
Proof.
  intros E c m x0 H1 H2 [H3 H4]. split.
  - intros y [x [H5 H6]]. subst y. specialize (H3 x H5). nra.
  - intros b H5. destruct (Rle_lt_dec 0 c) as [H6|H6].
    + assert (c = 0) by lra. subst c. assert (b <= 0). { apply Rge_le, H5. exists x0; split; auto; lra. } lra.
    + assert (is_upper_bound E (b / c)) as H7.
      { intros x H8. assert (H9 : b <= c * x). { apply Rge_le, H5. exists x; split; auto; lra. }
        apply Rmult_le_compat_neg_l with (r := / c) in H9; [|apply Rlt_le, Rinv_lt_0_compat; lra].
        replace (/ c * (c * x)) with x in H9 by (field; lra).
        replace (/ c * b) with (b / c) in H9 by (field; lra). auto. }
      specialize (H4 _ H7). apply Rmult_le_compat_neg_l with (r := c) in H4; [|lra].
      replace (c * (b / c)) with b in H4 by (field; lra). lra.
Qed.

Lemma is_lub_mult_neg : forall E c m x0,
  c <= 0 -> E x0 -> is_glb E m -> is_lub (fun y => exists x, E x /\ y = c * x) (c * m).
Proof.
  intros E c m x0 H1 H2 [H3 H4]. split.
  - intros y [x [H5 H6]]. subst y. specialize (H3 x H5). apply Rmult_le_compat_neg_l; lra.
  - intros b H5. destruct (Rle_lt_dec 0 c) as [H6|H6].
    + assert (c = 0) by lra. subst c. assert (0 <= b). { apply H5. exists x0; split; auto; lra. } lra.
    + assert (is_lower_bound E (b / c)) as H7.
      { intros x H8. assert (H9 : c * x <= b). { apply H5. exists x; split; auto; lra. }
        apply Rmult_le_compat_neg_l with (r := / c) in H9; [|apply Rlt_le, Rinv_lt_0_compat; lra].
        replace (/ c * (c * x)) with x in H9 by (field; lra).
        replace (/ c * b) with (b / c) in H9 by (field; lra). lra. }
      specialize (H4 _ H7). apply Rge_le, Rmult_le_compat_neg_l with (r := c) in H4; [|lra].
      replace (c * (b / c)) with b in H4 by (field; lra). auto.
Qed.

Lemma is_glb_sum : forall E1 E2 m1 m2,
  is_glb E1 m1 -> is_glb E2 m2 -> is_glb (fun y => exists x1 x2, E1 x1 /\ E2 x2 /\ y = x1 + x2) (m1 + m2).
Proof.
  intros E1 E2 m1 m2 [H1 H2] [H3 H4]. split.
  - intros y [x1 [x2 [H5 [H6 H7]]]]. subst y. specialize (H1 x1 H5). specialize (H3 x2 H6). lra.
  - intros b H5. assert (H6 : is_lower_bound E1 (b - m2)).
    { intros x1 H6. assert (H7 : is_lower_bound E2 (b - x1)).
      { intros x2 H7. assert (H8 : b <= x1 + x2). { apply Rge_le, H5. exists x1, x2. auto. } lra. }
      specialize (H4 (b - x1) H7). lra. }
    specialize (H2 (b - m2) H6). lra.
Qed.

Lemma is_lub_sum : forall E1 E2 M1 M2,
  is_lub E1 M1 -> is_lub E2 M2 -> is_lub (fun y => exists x1 x2, E1 x1 /\ E2 x2 /\ y = x1 + x2) (M1 + M2).
Proof.
  intros E1 E2 M1 M2 [H1 H2] [H3 H4]. split.
  - intros y [x1 [x2 [H5 [H6 H7]]]]. subst y. specialize (H1 x1 H5). specialize (H3 x2 H6). lra.
  - intros b H5. assert (H6 : is_upper_bound E1 (b - M2)).
    { intros x1 H6. assert (H7 : is_upper_bound E2 (b - x1)).
      { intros x2 H7. assert (H8 : x1 + x2 <= b). { apply H5. exists x1, x2. auto. } lra. }
      specialize (H4 (b - x1) H7). lra. }
    specialize (H2 (b - M2) H6). lra.
Qed.

Lemma glb_add_le : forall (E1 E2 E3 : Ensemble ℝ) m1 m2 m3,
  is_glb E1 m1 -> is_glb E2 m2 -> is_glb E3 m3 ->
  E3 ⊆ (fun y => exists x1 x2, E1 x1 /\ E2 x2 /\ y = x1 + x2) ->
  m1 + m2 <= m3.
Proof.
  intros E1 E2 E3 m1 m2 m3 H1 H2 H3 H4.
  eapply glb_subset with (E2 := fun y => exists x1 x2, E1 x1 /\ E2 x2 /\ y = x1 + x2); eauto.
  apply is_glb_sum; auto.
Qed.

Lemma lub_add_le : forall (E1 E2 E3 : Ensemble ℝ) M1 M2 M3,
  is_lub E1 M1 -> is_lub E2 M2 -> is_lub E3 M3 ->
  E3 ⊆ (fun y => exists x1 x2, E1 x1 /\ E2 x2 /\ y = x1 + x2) ->
  M3 <= M1 + M2.
Proof.
  intros E1 E2 E3 M1 M2 M3 H1 H2 H3 H4.
  eapply lub_subset with (E2 := fun y => exists x1 x2, E1 x1 /\ E2 x2 /\ y = x1 + x2); eauto.
  apply is_lub_sum; auto.
Qed.