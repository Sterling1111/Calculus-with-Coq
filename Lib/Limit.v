From Lib Require Import Imports Sequence Sets Reals_util Notations Functions Interval.
Import SetNotations IntervalNotations FunctionNotations.

Open Scope R_scope.

Definition limit (f : ℝ -> ℝ) (a L : ℝ) : Prop :=
  ∀ ε, ε > 0 -> ∃ δ, δ > 0 /\ ∀ x, 0 < |x - a| < δ -> |f x - L| < ε.

Definition left_limit (f : ℝ -> ℝ) (a L : ℝ) : Prop :=
  ∀ ε, ε > 0 -> ∃ δ, δ > 0 /\ ∀ x, 0 < a - x < δ -> |f x - L| < ε.

Definition right_limit (f : ℝ -> ℝ) (a L : ℝ) : Prop :=
  ∀ ε, ε > 0 -> ∃ δ, δ > 0 /\ ∀ x, 0 < x - a < δ -> |f x - L| < ε.

Definition limit_on (f : ℝ -> ℝ) (D : Ensemble ℝ) (a L : ℝ) : Prop :=
  ∀ ε, ε > 0 -> ∃ δ, δ > 0 /\ ∀ x, x ∈ D -> 0 < |x - a| < δ -> |f x - L| < ε.

Definition limit_to_pinf (f : ℝ -> ℝ) (a : ℝ) : Prop :=
  ∀ M : ℝ, ∃ δ, δ > 0 /\ ∀ x, 0 < |x - a| < δ -> f x > M.

Definition limit_to_minf (f : ℝ -> ℝ) (a : ℝ) : Prop :=
  ∀ M : ℝ, ∃ δ, δ > 0 /\ ∀ x, 0 < |x - a| < δ -> f x < M.

Definition right_limit_to_pinf (f : ℝ -> ℝ) (a : ℝ) : Prop :=
  ∀ M : ℝ, ∃ δ, δ > 0 /\ ∀ x, 0 < x - a < δ -> f x > M.

Definition right_limit_to_minf (f : ℝ -> ℝ) (a : ℝ) : Prop :=
  ∀ M : ℝ, ∃ δ, δ > 0 /\ ∀ x, 0 < x - a < δ -> f x < M.

Definition left_limit_to_pinf (f : ℝ -> ℝ) (a : ℝ) : Prop :=
  ∀ M : ℝ, ∃ δ, δ > 0 /\ ∀ x, 0 < a - x < δ -> f x > M.

Definition left_limit_to_minf (f : ℝ -> ℝ) (a : ℝ) : Prop :=
  ∀ M : ℝ, ∃ δ, δ > 0 /\ ∀ x, 0 < a - x < δ -> f x < M.

Definition limit_pinf (f : ℝ -> ℝ) (L : ℝ) : Prop :=
  ∀ ε, ε > 0 -> ∃ N, ∀ x, x > N -> |f x - L| < ε.

Definition limit_minf (f : ℝ -> ℝ) (L : ℝ) : Prop :=
  ∀ ε, ε > 0 -> ∃ N, ∀ x, x < N -> |f x - L| < ε.

Definition limit_pinf_to_pinf (f : ℝ -> ℝ) : Prop :=
  ∀ M : ℝ, ∃ N, ∀ x, x > N -> f x > M.

Definition limit_pinf_to_minf (f : ℝ -> ℝ) : Prop :=
  ∀ M : ℝ, ∃ N, ∀ x, x > N -> f x < M.

Definition limit_minf_to_pinf (f : ℝ -> ℝ) : Prop :=
  ∀ M : ℝ, ∃ N, ∀ x, x < N -> f x > M.

Definition limit_minf_to_minf (f : ℝ -> ℝ) : Prop :=
  ∀ M : ℝ, ∃ N, ∀ x, x < N -> f x < M.

Module LimitNotations.

  Declare Scope limit_scope.
  Delimit Scope limit_scope with lim.

  Notation "⟦ 'lim' a ⟧ f '=' L" := 
    (limit f a L) 
      (at level 70, f at level 0, no associativity, format "⟦  'lim'  a  ⟧  f  '='  L") : limit_scope.

  Notation "⟦ 'lim' a ⁺ ⟧ f '=' L" := 
    (right_limit f a L)
      (at level 70, f at level 0, no associativity, format "⟦  'lim'  a ⁺  ⟧  f  '='  L") : limit_scope.

  Notation "⟦ 'lim' a ⁻ ⟧ f '=' L" :=
    (left_limit f a L)
      (at level 70, f at level 0, no associativity, format "⟦  'lim'  a ⁻  ⟧  f  '='  L") : limit_scope.

  Notation "⟦ 'lim' a ⟧ f D '=' L" :=
    (limit_on f D a L)
      (at level 70, f at level 0, D at level 0, no associativity, format "⟦  'lim'  a  ⟧  f  D  '='  L") : limit_scope.

  Notation "⟦ 'lim' ∞ ⟧ f '=' L" :=
    (limit_pinf f L)
      (at level 70, f at level 0, no associativity, format "⟦  'lim'  ∞  ⟧  f  '='  L") : limit_scope.

  Notation "⟦ 'lim' ∞ ⟧ f '=' ∞" :=
    (limit_pinf_to_pinf f)
      (at level 70, f at level 0, no associativity, format "⟦  'lim'  ∞  ⟧  f  '='  ∞") : limit_scope.

  Notation "⟦ 'lim' ∞ ⟧ f '=' -∞" :=
    (limit_pinf_to_minf f)
      (at level 70, f at level 0, no associativity, format "⟦  'lim'  ∞  ⟧  f  '='  -∞") : limit_scope.

  Notation "⟦ 'lim' -∞ ⟧ f '=' L" :=
    (limit_minf f L)
      (at level 70, f at level 0, no associativity, format "⟦  'lim'  -∞  ⟧  f  '='  L") : limit_scope.

  Notation "⟦ 'lim' -∞ ⟧ f '=' ∞" :=
    (limit_minf_to_pinf f)
      (at level 70, f at level 0, no associativity, format "⟦  'lim'  -∞  ⟧  f  '='  ∞") : limit_scope.

  Notation "⟦ 'lim' -∞ ⟧ f '=' -∞" :=
    (limit_minf_to_minf f)
      (at level 70, f at level 0, no associativity, format "⟦  'lim'  -∞  ⟧  f  '='  -∞") : limit_scope.

  Notation "⟦ 'lim' a ⟧ f '=' ∞" :=
    (limit_to_pinf f a)
      (at level 70, f at level 0, no associativity, format "⟦  'lim'  a  ⟧  f  '='  ∞") : limit_scope.

  Notation "⟦ 'lim' a ⟧ f '=' -∞" :=
    (limit_to_minf f a)
      (at level 70, f at level 0, no associativity, format "⟦  'lim'  a  ⟧  f  '='  -∞") : limit_scope.

  Notation "⟦ 'lim' a ⁺ ⟧ f '=' ∞" :=
    (right_limit_to_pinf f a)
      (at level 70, f at level 0, no associativity, format "⟦  'lim'  a ⁺  ⟧  f  '='  ∞") : limit_scope.

  Notation "⟦ 'lim' a ⁺ ⟧ f '=' -∞" :=
    (right_limit_to_minf f a)
      (at level 70, f at level 0, no associativity, format "⟦  'lim'  a ⁺  ⟧  f  '='  -∞") : limit_scope.

  Notation "⟦ 'lim' a ⁻ ⟧ f '=' ∞" :=
    (left_limit_to_pinf f a)
      (at level 70, f at level 0, no associativity, format "⟦  'lim'  a ⁻  ⟧  f  '='  ∞") : limit_scope.

  Notation "⟦ 'lim' a ⁻ ⟧ f '=' -∞" :=
    (left_limit_to_minf f a)
      (at level 70, f at level 0, no associativity, format "⟦  'lim'  a ⁻  ⟧  f  '='  -∞") : limit_scope.

  Open Scope limit_scope.
      
End LimitNotations.

Import LimitNotations.

Lemma lemma_1_20 : forall x x0 y y0 ε,
  |x - x0| < ε / 2 -> |y - y0| < ε / 2 -> |(x + y) - (x0 + y0)| < ε /\ |(x - y) - (x0 - y0)| < ε.
Proof.
  solve_abs.
Qed.

Lemma lemma_1_21 : forall x x0 y y0 ε,
  |x - x0| < Rmin (ε / (2 * (|y0| + 1))) 1 -> |y - y0| < ε / (2 * (|x0| + 1)) -> |x * y - x0 * y0| < ε.
Proof.
  intros x x0 y y0 ε H1 H2. assert (H3 : (|x - x0|) < 1). { apply Rlt_gt in H1. apply Rmin_Rgt_l in H1. lra. }
  assert (H4 : |x| - |x0| < 1). { pose proof Rabs_triang_inv x x0. lra. }
  assert (H5 : |y - y0| >= 0) by (apply Rle_ge; apply Rabs_pos).
  assert (H6 : |x0| >= 0) by (apply Rle_ge; apply Rabs_pos).
  assert (H7 : ε > 0).
  { 
    pose proof Rtotal_order ε 0 as [H7 | [H7 | H7]].
    - assert (H8 : ε / (2 * (|x0| + 1)) < 0). { apply Rdiv_neg_pos. lra. lra. } lra.
    - nra.
    - apply H7.
  }
  assert (H8 : |x| < 1 + |x0|) by lra. replace (x * y - x0 * y0) with (x * (y - y0) + y0 * (x - x0)) by lra.
  assert (H9 : |x * (y - y0) + y0 * (x - x0)| <= |x| * |y - y0| + |y0| * |x - x0|) by solve_abs.
  assert (H10 : (1 + |x0|) * (ε / (2 * (|x0| + 1))) = ε / 2). { field; try unfold Rabs; try destruct Rcase_abs; try nra. }
  assert (H11 : forall x, x >= 0 -> x / (2 * (x + 1)) < 1 / 2).
  {
    intros x1 H11. apply Rmult_lt_reg_l with (r := 2). lra. unfold Rdiv.
    replace (2 * (1 * / 2)) with (1) by lra. replace (2 * (x1 * / (2 * (x1 + 1)))) with ((x1) * (2 * / (2 * (x1 + 1)))) by lra.
    rewrite Rinv_mult. replace (2 * (/ 2 * / (x1 + 1))) with (2 * / 2 * / (x1 + 1)) by nra. rewrite Rinv_r. 2 : lra.
    rewrite Rmult_1_l. rewrite <- Rdiv_def. apply Rdiv_lt_1. lra. lra.
  }
  assert (H12 : (|y0| * (ε / (2 * (|y0| + 1)))) < ε / 2). 
  { 
    replace (|y0| * (ε / (2 * (|y0| + 1)))) with (ε * (|y0| * / (2 * (|y0| + 1)))) by lra.
    pose proof H11 (|y0|) as H12. unfold Rdiv. apply Rmult_lt_compat_l. lra. unfold Rdiv in H12. rewrite Rmult_1_l in H12.
    apply H12. apply Rle_ge. apply Rabs_pos.
  }
  replace (ε) with (ε / 2 + ε / 2) by lra. 
  assert (H13 : |x| * |y - y0| < ((1 + |x0|) * (ε / (2 * (|x0| + 1))))) by nra.
  assert (H14 : |x - x0| < (ε / (2 * (|y0| + 1)))). { apply Rlt_gt in H1. apply Rmin_Rgt_l in H1. lra. }
  assert (H15 : |y0| >= 0) by (apply Rle_ge; apply Rabs_pos).
  assert (H16 : |x - x0| >= 0) by (apply Rle_ge; apply Rabs_pos).
  assert (H17 : |y0| * |x - x0| <= (|y0| * (ε / (2 * (|y0| + 1))))) by nra.
  nra.
Qed.

Lemma lemma_1_22 : forall y y0 ε,
  y0 <> 0 -> |y - y0| < Rmin (|y0| / 2) ((ε * |y0|^2) / 2) -> y <> 0 /\ |1 / y - 1 / y0| < ε.
Proof.
  intros y y0 eps H1 H2. assert (H3 : y <> 0).
  - assert (H4 : |y - y0| < |y0 / 2|). { apply Rlt_gt in H2. apply Rmin_Rgt_l in H2. solve_abs. } solve_abs.
  - split.
    -- apply H3.
    -- assert (H4 : |y - y0| < |y0 / 2|). { apply Rlt_gt in H2. apply Rmin_Rgt_l in H2. solve_abs. }
       assert (H5 : |y - y0| < (eps * (|y0|)^2) / 2). { apply Rlt_gt in H2. apply Rmin_Rgt_l in H2. lra. }
       assert (H6 : |y| > |y0| / 2) by solve_abs.
       assert (H7 : |y| > 0) by solve_abs. assert (H8 : |y0| > 0) by solve_abs.
       assert (H9 : forall a b : R, a > 0 -> b > 0 -> a > b / 2 -> 1 / a < 2 / b).
       { 
         intros a b H9 H10 H11. apply Rmult_lt_reg_r with (r := a). lra. replace (1 / a * a) with 1 by (field; lra).
         apply Rmult_lt_reg_r with (r := b). lra. replace (2 / b * a * b) with (2 * a) by (field; lra). lra.
       }
       assert (H10 : 1 / |y| < 2 / |y0|). { apply H9. apply H7. apply H8. apply H6. } clear H9.
       replace (1 / y - 1 / y0) with ((y0 - y) / (y * y0)) by (field; lra). 
       unfold Rdiv. rewrite Rabs_mult. rewrite Rabs_inv. rewrite <- Rdiv_def. rewrite Rabs_mult.
       rewrite Rabs_minus_sym. assert (H11 : 2 * |y - y0| < eps * |y0| ^ 2). { lra. }
       assert (H12 : (2 * |y - y0|) / (|y0| ^ 2) < eps).
       { apply Rmult_lt_reg_r with (r := |y0| ^ 2). nra. apply Rmult_lt_reg_r with (r := / 2). nra.
         replace (2 * |y - y0| / (|y0| ^ 2) * |y0| ^2 * / 2) with 
         (2 * |y - y0| * / 2) by (field; lra). lra.
       }
       replace (2 * |y - y0| / |y0| ^ 2) with (|y - y0| / ((|y0| / 2) * |y0|)) in H12 by (field; nra).
       assert (H13 : (|y0| / 2 * |y0|) < |y| * |y0|) by nra. 
       assert (H14 : forall a b c, a > 0 -> b > 0 -> c >= 0 -> a > b -> c / a <= c / b).
       {
         intros a b c H14 H15 H16 H17. apply Rmult_le_reg_r with (r := a). lra.
         replace (c / a * a) with c by (field; lra). apply Rmult_le_reg_r with (r := b). lra.
         replace (c / b * a * b) with (c * a) by (field; lra). nra.
       }
       assert (H15 : |y - y0| / (|y0| / 2 * |y0|) >= |y - y0| / (|y| * |y0|)). 
       { apply Rle_ge. apply H14. nra. nra. apply Rle_ge. apply Rabs_pos. nra. }
       nra.
Qed.

Lemma limit_eq : forall f1 f2 a L,
  (exists δ, δ > 0 /\ forall x, 0 < |x - a| < δ -> f1 x = f2 x) ->
  ⟦ lim a ⟧ f1 = L -> ⟦ lim a ⟧ f2 = L.
Proof.
  intros f1 f2 a L [δ1 [H1 H2]] H3 ε H4.
  specialize (H3 ε H4) as [δ2 [H5 H6]].
  exists (Rmin δ1 δ2). split; [solve_R |].
  intros x H7. rewrite <- H2; [apply H6 |]; solve_R.
Qed.

Lemma limit_eq' : forall f1 f2 a L,
  (forall x, f1 x = f2 x) -> ⟦ lim a ⟧ f1 = L -> ⟦ lim a ⟧ f2 = L.
Proof.
  intros f1 f2 a L H1 H2. replace f2 with f1 by (extensionality x; apply H1). exact H2.
Qed.

Lemma limit_left_eq : forall f1 f2 a L,
  (exists δ, δ > 0 /\ forall x, 0 < a - x < δ -> f1 x = f2 x) ->
  ⟦ lim a⁻ ⟧ f1 = L -> ⟦ lim a⁻ ⟧ f2 = L.
Proof.
  intros f1 f2 a L [δ1 [H1 H2]] H3 ε H4.
  specialize (H3 ε H4) as [δ2 [H5 H6]].
  exists (Rmin δ1 δ2). split; [solve_R |].
  intros x H7. rewrite <- H2; [apply H6 |]; solve_R.
Qed.

Lemma limit_right_eq : forall f1 f2 a L,
  (exists δ, δ > 0 /\ forall x, 0 < x - a < δ -> f1 x = f2 x) ->
  ⟦ lim a⁺ ⟧ f1 = L -> ⟦ lim a⁺ ⟧ f2 = L.
Proof.
  intros f1 f2 a L [δ1 [H1 H2]] H3 ε H4.
  specialize (H3 ε H4) as [δ2 [H5 H6]].
  exists (Rmin δ1 δ2). split; [solve_R |].
  intros x H7. rewrite <- H2; [apply H6 |]; solve_R.
Qed.

Lemma limit_on_eq : forall f1 f2 D a L,
  (forall x, x ∈ D -> f1 x = f2 x) ->
  ⟦ lim a ⟧ f1 D = L -> ⟦ lim a ⟧ f2 D = L.
Proof.
  intros f1 f2 D a L H1 H2 ε H3.
  specialize (H2 ε H3) as [δ [H4 H5]].
  exists δ. split; [solve_R |].
  intros x H6 H7. rewrite <- H1; [apply H5 |]; solve_R.
Qed.

Lemma limit_ext : forall f g a L, 
  (forall x, f x = g x) -> ⟦ lim a ⟧ f = L -> ⟦ lim a ⟧ g = L.
Proof.
  intros f g a L H H0. eapply limit_eq; eauto. exists 1. split; [lra|intros; apply H].
Qed.

Lemma right_limit_ext : forall f g a L, 
  (forall x, f x = g x) -> ⟦ lim a ⁺ ⟧ f = L -> ⟦ lim a ⁺ ⟧ g = L.
Proof.
  intros f g a L H H0. eapply limit_right_eq; eauto. exists 1. split; [lra|intros; apply H].
Qed.

Lemma left_limit_ext : forall f g a L, 
  (forall x, f x = g x) -> ⟦ lim a ⁻ ⟧ f = L -> ⟦ lim a ⁻ ⟧ g = L.
Proof.
  intros f g a L H H0. eapply limit_left_eq; eauto. exists 1. split; [lra|intros; apply H].
Qed.

Lemma limit_subst : forall f a L1 L2,
  L1 = L2 -> ⟦ lim a ⟧ f = L1 -> ⟦ lim a ⟧ f = L2.
Proof. intros f a L1 L2 -> H. exact H. Qed.

Lemma limit_unique : forall f a L1 L2,
  ⟦ lim a ⟧ f = L1 -> ⟦ lim a ⟧ f = L2 -> L1 = L2. 
Proof.
  intros f a L1 L2 H1 H2. pose proof (classic (L1 = L2)) as [H3 | H3]; auto.
  specialize (H1 (|L1 - L2| / 2) ltac:(solve_abs)) as [δ1 [H4 H5]].
  specialize (H2 (|L1 - L2| / 2) ltac:(solve_abs)) as [δ2 [H6 H7]].
  set (δ := Rmin δ1 δ2). set (x := a + δ / 2). assert (δ <= δ1 /\ δ <= δ2) as [H8 H9] by (unfold δ; solve_min).
  assert (0 < δ / 2) as H10 by (apply Rdiv_pos_pos; solve_R). assert (x > a) as H11 by (unfold x; solve_min).
  assert (0 < |x - a| < δ) as H12 by (unfold x; solve_R). specialize (H5 x ltac:(solve_R)). specialize (H7 x ltac:(solve_R)).
  assert (|L1 - L2| < |L1 - L2|) as H13.
  {
    assert (|(L1 - f x + (f x - L2))| <= |L1 - f x| + |f x - L2|) as H22 by (apply Rabs_triang).
    rewrite Rabs_minus_sym in H22. 
    assert (|f x - L1| + |f x - L2| < |L1 - L2| / 2 + |L1 - L2| / 2) as H23 by lra.
    field_simplify in H23. rewrite Rmult_div_r in H23; auto.
    replace (L1 - f x + (f x - L2)) with (L1 - L2) in H22 by lra. lra.
  } lra.
Qed.

Lemma limit_left_unique : forall f a L1 L2,
  ⟦ lim a⁻ ⟧ f = L1 -> ⟦ lim a⁻ ⟧ f = L2 -> L1 = L2.
Proof.
  intros f a L1 L2 H1 H2. pose proof (classic (L1 = L2)) as [H3 | H3]; auto.
  specialize (H1 (|L1 - L2| / 2) ltac:(solve_abs)) as [δ1 [H4 H5]].
  specialize (H2 (|L1 - L2| / 2) ltac:(solve_abs)) as [δ2 [H6 H7]].
  set (δ := Rmin δ1 δ2). set (x := a - δ / 2). assert (δ <= δ1 /\ δ <= δ2) as [H8 H9] by (unfold δ; solve_min).
  assert (0 < δ / 2) as H10 by (apply Rdiv_pos_pos; solve_R). assert (x < a) as H11 by (unfold x; solve_min).
  assert (0 < |x - a| < δ) as H12 by (unfold x; solve_R). specialize (H5 x ltac:(solve_R)). specialize (H7 x ltac:(solve_R)).
  assert (|L1 - L2| < |L1 - L2|) as H13.
  {
    assert (|(L1 - f x + (f x - L2))| <= |L1 - f x| + |f x - L2|) as H22 by (apply Rabs_triang).
    rewrite Rabs_minus_sym in H22. 
    assert (|f x - L1| + |f x - L2| < |L1 - L2| / 2 + |L1 - L2| / 2) as H23 by lra.
    field_simplify in H23. rewrite Rmult_div_r in H23; auto.
    replace (L1 - f x + (f x - L2)) with (L1 - L2) in H22 by lra. lra.
  } lra.
Qed.

Lemma limit_right_unique : forall f a L1 L2,
  ⟦ lim a⁺ ⟧ f = L1 -> ⟦ lim a⁺ ⟧ f = L2 -> L1 = L2.
Proof.
  intros f a L1 L2 H1 H2. pose proof (classic (L1 = L2)) as [H3 | H3]; auto.
  specialize (H1 (|L1 - L2| / 2) ltac:(solve_abs)) as [δ1 [H4 H5]].
  specialize (H2 (|L1 - L2| / 2) ltac:(solve_abs)) as [δ2 [H6 H7]].
  set (δ := Rmin δ1 δ2). set (x := a + δ / 2). assert (δ <= δ1 /\ δ <= δ2) as [H8 H9] by (unfold δ; solve_min).
  assert (0 < δ / 2) as H10 by (apply Rdiv_pos_pos; solve_R). assert (x > a) as H11 by (unfold x; solve_min).
  assert (0 < |x - a| < δ) as H12 by (unfold x; solve_R). specialize (H5 x ltac:(solve_R)). specialize (H7 x ltac:(solve_R)).
  assert (|L1 - L2| < |L1 - L2|) as H13.
  {
    assert (|(L1 - f x + (f x - L2))| <= |L1 - f x| + |f x - L2|) as H22 by (apply Rabs_triang).
    rewrite Rabs_minus_sym in H22. 
    assert (|f x - L1| + |f x - L2| < |L1 - L2| / 2 + |L1 - L2| / 2) as H23 by lra.
    field_simplify in H23. rewrite Rmult_div_r in H23; auto.
    replace (L1 - f x + (f x - L2)) with (L1 - L2) in H22 by lra. lra.
  } lra.
Qed.

Lemma limit_iff : forall f a L,
  ⟦ lim a ⟧ f = L <-> ⟦ lim a⁻ ⟧ f = L ∧ ⟦ lim a⁺ ⟧ f = L.
Proof.
  intros f a L. split.
  - intros H1. split.
    -- intros ε H2. specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto. intros x H5. specialize (H4 x). solve_R.
    -- intros ε H2. specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto. intros x H5. specialize (H4 x). solve_R.
  - intros [H1 H2] ε H3. specialize (H1 ε H3) as [δ1 [H4 H5]]. specialize (H2 ε H3) as [δ2 [H6 H7]]. set (δ := Rmin δ1 δ2).
    assert (δ > 0) as H8 by (unfold δ; solve_min). assert (δ <= δ1 /\ δ <= δ2) as [H9 H10] by (unfold δ; solve_min).
    exists δ. split; auto. intros x H11. specialize (H5 x). specialize (H7 x). solve_R.
Qed.

Lemma limit_imp_limit_on : forall f L D a,
  ⟦ lim a ⟧ f = L -> ⟦ lim a ⟧ f D = L.
Proof.
  intros f L D a H1 ε H2. 
  specialize (H1 ε H2) as [δ [H3 H4]]. 
  exists δ; split; auto. 
Qed.

Lemma limit_on_R_iff : forall f a L,
  ⟦ lim a ⟧ f ℝ = L <-> ⟦ lim a ⟧ f = L.
Proof.
  intros f a L. split.
  - intros H1 ε H2. specialize (H1 ε H2) as [δ [H3 H4]]. exists δ; split; auto. intros x H5. specialize (H4 x ltac:(apply Full_intro)). solve_R.
  - intros H1 ε H2. specialize (H1 ε H2) as [δ [H3 H4]]. exists δ; split; auto.
Qed.

Lemma limit_const : forall a c, ⟦ lim a ⟧ (fun _ => c) = c.
Proof. intros a c ε H1. exists 1. split; solve_abs. Qed.

Lemma limit_left_const : forall a c, ⟦ lim a⁻ ⟧ (fun _ => c) = c.
Proof. intros a c ε H1. exists 1. split; solve_abs. Qed.

Lemma limit_right_const : forall a c, ⟦ lim a⁺ ⟧ (fun _ => c) = c.
Proof. intros a c ε H1. exists 1. split; solve_abs. Qed.

Lemma limit_on_const : forall a D c, ⟦ lim a ⟧ (fun _ => c) D = c.
Proof. intros a D c ε H1. exists 1. split; solve_abs. Qed.

Lemma limit_id : forall a, ⟦ lim a ⟧ (fun x => x) = a.
Proof. intros a ε H1. exists ε. split; solve_abs. Qed.

Lemma limit_left_id : forall a, ⟦ lim a⁻ ⟧ (fun x => x) = a.
Proof. intros a ε H1. exists ε. split; solve_abs. Qed.

Lemma limit_right_id : forall a, ⟦ lim a⁺ ⟧ (fun x => x) = a.
Proof. intros a ε H1. exists ε. split; solve_abs. Qed.

Lemma limit_on_id : forall a D, ⟦ lim a ⟧ (fun x => x) D = a.
Proof. intros a D ε H1. exists ε. split; solve_abs. Qed.

Lemma limit_left_neg : forall f a L,
  ⟦ lim a⁻ ⟧ f = L -> ⟦ lim a⁻ ⟧ (- f) = - L.
Proof.
  intros f a L H1 ε H2. specialize (H1 ε ltac:(lra)) as [δ [H3 H4]].
  exists δ. split; try lra. intros x H5. specialize (H4 x H5).
  solve_R.
Qed.

Lemma limit_right_neg : forall f a L,
  ⟦ lim a⁺ ⟧ f = L -> ⟦ lim a⁺ ⟧ (- f) = - L.
Proof.
  intros f a L H1 ε H2. specialize (H1 ε ltac:(lra)) as [δ [H3 H4]].
  exists δ. split; try lra. intros x H5. specialize (H4 x H5).
  solve_R.
Qed.

Lemma limit_neg : forall f a L,
  ⟦ lim a ⟧ f = L -> ⟦ lim a ⟧ (- f) = - L.
Proof.
  intros f a L H1. apply limit_iff in H1 as [H2 H3].
  apply limit_iff; split; [ apply limit_left_neg | apply limit_right_neg ]; auto.
Qed.

Lemma limit_left_plus : forall f1 f2 a L1 L2,
  ⟦ lim a⁻ ⟧ f1 = L1 -> ⟦ lim a⁻ ⟧ f2 = L2 -> ⟦ lim a⁻ ⟧ (f1 + f2) = (L1 + L2).
Proof.
  intros f1 f2 a L1 L2 H1 H2 ε H3. specialize (H1 (ε / 2) ltac:(lra)) as [δ1 [H4 H5]].
  specialize (H2 (ε / 2) ltac:(lra)) as [δ2 [H6 H7]]. set (δ := Rmin δ1 δ2).
  assert (δ > 0) as H8 by (unfold δ; solve_min). exists δ. split; try lra.
  intros x H9. specialize (H5 x ltac:(unfold δ in *; solve_R)). specialize (H7 x ltac:(unfold δ in *; solve_R)).
  solve_R.
Qed.

Lemma limit_right_plus : forall f1 f2 a L1 L2,
  ⟦ lim a⁺ ⟧ f1 = L1 -> ⟦ lim a⁺ ⟧ f2 = L2 -> ⟦ lim a⁺ ⟧ (f1 + f2) = (L1 + L2).
Proof.
  intros f1 f2 a L1 L2 H1 H2 ε H3. specialize (H1 (ε / 2) ltac:(lra)) as [δ1 [H4 H5]].
  specialize (H2 (ε / 2) ltac:(lra)) as [δ2 [H6 H7]]. set (δ := Rmin δ1 δ2).
  assert (δ > 0) as H8 by (unfold δ; solve_min). exists δ. split; try lra.
  intros x H9. specialize (H5 x ltac:(unfold δ in *; solve_R)). specialize (H7 x ltac:(unfold δ in *; solve_R)).
  solve_R.
Qed.

Lemma limit_plus : forall f1 f2 a L1 L2,
  ⟦ lim a ⟧ f1 = L1 -> ⟦ lim a ⟧ f2 = L2 -> ⟦ lim a ⟧ (f1 + f2) = (L1 + L2).
Proof.
  intros f1 f2 a L1 L2 H1 H2. apply limit_iff in H1 as [H3 H4], H2 as [H5 H6].
  apply limit_iff; split; [ apply limit_left_plus | apply limit_right_plus ]; auto.
Qed.

Lemma limit_on_plus : forall f1 f2 a D L1 L2,
  ⟦ lim a ⟧ f1 D = L1 -> ⟦ lim a ⟧ f2 D = L2 -> ⟦ lim a ⟧ (f1 + f2) D = (L1 + L2).
Proof.
  intros f1 f2 a D L1 L2 H1 H2 ε H3. specialize (H1 (ε / 2) ltac:(lra)) as [δ1 [H4 H5]].
  specialize (H2 (ε / 2) ltac:(lra)) as [δ2 [H6 H7]]. set (δ := Rmin δ1 δ2).
  assert (δ > 0) as H8 by (unfold δ; solve_min). exists δ. split; try lra.
  intros x H9 H10. specialize (H5 x ltac:(unfold δ in *; solve_R) ltac:(unfold δ in *; solve_R)).
  specialize (H7 x ltac:(unfold δ in *; solve_R) ltac:(unfold δ in *; solve_R)). 
  solve_R.
Qed.

Lemma limit_left_minus : forall f1 f2 a L1 L2,
  ⟦ lim a⁻ ⟧ f1 = L1 -> ⟦ lim a⁻ ⟧ f2 = L2 -> ⟦ lim a⁻ ⟧ (f1 - f2) = (L1 - L2).
Proof.
  intros f1 f2 a L1 L2 H1 H2. unfold Rminus. apply limit_left_plus; auto.
  intros ε H3. specialize (H2 ε H3) as [δ [H4 H5]].
  exists δ. split; auto. intros x H6. apply H5 in H6. solve_abs.
Qed.

Lemma limit_right_minus : forall f1 f2 a L1 L2,
  ⟦ lim a⁺ ⟧ f1 = L1 -> ⟦ lim a⁺ ⟧ f2 = L2 -> ⟦ lim a⁺ ⟧ (f1 - f2) = (L1 - L2).
Proof.
  intros f1 f2 a L1 L2 H1 H2. unfold Rminus. apply limit_right_plus; auto.
  intros ε H3. specialize (H2 ε H3) as [δ [H4 H5]].
  exists δ. split; auto. intros x H6. apply H5 in H6. solve_abs.
Qed.

Lemma limit_minus : forall f1 f2 a L1 L2,
  ⟦ lim a ⟧ f1 = L1 -> ⟦ lim a ⟧ f2 = L2 -> ⟦ lim a ⟧ (f1 - f2) = (L1 - L2).
Proof.
  intros f1 f2 a L1 L2 H1 H2. apply limit_iff in H1 as [H3 H4], H2 as [H5 H6].
  apply limit_iff; split; [ apply limit_left_minus | apply limit_right_minus ]; auto.
Qed.

Lemma limit_on_minus : forall f1 f2 a D L1 L2,
  ⟦ lim a ⟧ f1 D = L1 -> ⟦ lim a ⟧ f2 D = L2 -> ⟦ lim a ⟧ (f1 - f2) D = (L1 - L2).
Proof.
  intros f1 f2 a D L1 L2 H1 H2 ε H3. specialize (H1 (ε / 2) ltac:(lra)) as [δ1 [H4 H5]].
  specialize (H2 (ε / 2) ltac:(lra)) as [δ2 [H6 H7]]. set (δ := Rmin δ1 δ2).
  assert (δ > 0) as H8 by (unfold δ; solve_min). exists δ. split; try lra.
  intros x H9 H10. specialize (H5 x ltac:(unfold δ in *; solve_R) ltac:(unfold δ in *; solve_R)).
  specialize (H7 x ltac:(unfold δ in *; solve_R) ltac:(unfold δ in *; solve_R)).
  solve_R.
Qed.

Lemma limit_left_mult : forall f1 f2 a L1 L2,
  ⟦ lim a⁻ ⟧ f1 = L1 -> ⟦ lim a⁻ ⟧ f2 = L2 -> ⟦ lim a⁻ ⟧ (f1 ⋅ f2) = L1 * L2.
Proof.
  intros f1 f2 a L1 L2 H1 H2 ε H3. assert (ε / (2 * ((|L2|) + 1)) > 0 /\ ε / (2 * ((|L1|) + 1)) > 0) as [H4 H5].
  { split; apply Rdiv_pos_pos; solve_abs. }
  specialize (H1 (Rmin (ε / (2 * ((|L2|) + 1))) 1) ltac:(solve_min)) as [δ1 [H6 H7]].
  specialize (H2 (ε / (2 * ((|L1|) + 1))) ltac:(solve_min)) as [δ2 [H8 H9]].
  set (δ := Rmin δ1 δ2). assert (δ > 0) as H10 by (unfold δ; solve_min). exists δ. split; try lra.
  intros x H11. assert (0 < a - x < δ1 /\ 0 < a - x < δ2) as [H12 H13] by (unfold δ in H11; solve_min).
  specialize (H7 x H12). specialize (H9 x H13). apply lemma_1_21; auto.
Qed.

Lemma limit_right_mult : forall f1 f2 a L1 L2,
  ⟦ lim a⁺ ⟧ f1 = L1 -> ⟦ lim a⁺ ⟧ f2 = L2 -> ⟦ lim a⁺ ⟧ (f1 ⋅ f2) = L1 * L2.
Proof.
  intros f1 f2 a L1 L2 H1 H2 ε H3. assert (ε / (2 * ((|L2|) + 1)) > 0 /\ ε / (2 * ((|L1|) + 1)) > 0) as [H4 H5].
  { split; apply Rdiv_pos_pos; solve_abs. }
  specialize (H1 (Rmin (ε / (2 * ((|L2|) + 1))) 1) ltac:(solve_min)) as [δ1 [H6 H7]].
  specialize (H2 (ε / (2 * ((|L1|) + 1))) ltac:(solve_min)) as [δ2 [H8 H9]].
  set (δ := Rmin δ1 δ2). assert (δ > 0) as H10 by (unfold δ; solve_min). exists δ. split; try lra.
  intros x H11. assert (0 < x - a < δ1 /\ 0 < x - a < δ2) as [H12 H13] by (unfold δ in H11; solve_min).
  specialize (H7 x H12). specialize (H9 x H13). apply lemma_1_21; auto.
Qed.

Lemma limit_mult : forall f1 f2 a L1 L2,
  ⟦ lim a ⟧ f1 = L1 -> ⟦ lim a ⟧ f2 = L2 -> ⟦ lim a ⟧ (f1 ⋅ f2) = L1 * L2.
Proof.
  intros f1 f2 a L1 L2 H1 H2. apply limit_iff in H1 as [H3 H4], H2 as [H5 H6].
  apply limit_iff; split; [ apply limit_left_mult | apply limit_right_mult ]; auto.
Qed.

Lemma limit_on_mult : forall f1 f2 a D L1 L2,
  ⟦ lim a ⟧ f1 D = L1 -> ⟦ lim a ⟧ f2 D = L2 -> ⟦ lim a ⟧ (f1 ⋅ f2) D = L1 * L2.
Proof.
  intros f1 f2 a D L1 L2 H1 H2 ε H3. assert (ε / (2 * ((|L2|) + 1)) > 0 /\ ε / (2 * ((|L1|) + 1)) > 0) as [H4 H5].
  { split; apply Rdiv_pos_pos; solve_abs. }
  specialize (H1 (Rmin (ε / (2 * ((|L2|) + 1))) 1) ltac:(solve_min)) as [δ1 [H6 H7]].
  specialize (H2 (Rmin (ε / (2 * ((|L1|) + 1))) 1) ltac:(solve_min)) as [δ2 [H8 H9]].
  set (δ := Rmin δ1 δ2). assert (δ > 0) as H10 by (unfold δ; solve_min). exists δ. split; try lra.
  intros x H11 H12. assert (0 < |x - a| < δ1 /\ 0 < |x - a| < δ2) as [H13 H14] by (unfold δ in *; solve_R).
  specialize (H7 x H11 H13). specialize (H9 x H11 H14). apply lemma_1_21; auto. solve_R.
Qed.

Lemma limit_left_mult_const_l : forall f c a L,
  ⟦ lim a ⁻ ⟧ f = L -> ⟦ lim a ⁻ ⟧ (fun x => c * f x) = c * L.
Proof.
  intros f c a L H1.
  apply limit_left_eq with (f1 := (fun _ => c) ⋅ f).
  - exists 1. split; solve_R.
  - apply limit_left_mult; auto. apply limit_left_const.
Qed.

Lemma limit_right_mult_const_l : forall f c a L,
  ⟦ lim a ⁺ ⟧ f = L -> ⟦ lim a ⁺ ⟧ (fun x => c * f x) = c * L.
Proof.
  intros f c a L H1.
  apply limit_right_eq with (f1 := (fun _ => c) ⋅ f).
  - exists 1. split; solve_R.
  - apply limit_right_mult; auto. apply limit_right_const.
Qed.

Lemma limit_mult_const_l : forall f c a L,
  ⟦ lim a ⟧ f = L -> ⟦ lim a ⟧ (fun x => c * f x) = c * L.
Proof.
  intros f c a L H1.
  apply limit_eq with (f1 := (fun _ => c) ⋅ f).
  - exists 1. split; solve_R.
  - apply limit_mult; auto. apply limit_const.
Qed.

Lemma limit_on_mult_const_l : forall f c a D L,
  ⟦ lim a ⟧ f D = L -> ⟦ lim a ⟧ (fun x => c * f x) D = c * L.
Proof.
  intros f c a D L H1.
  apply limit_on_eq with (f1 := (fun _ => c) ⋅ f).
  - intros x H2. reflexivity.
  - apply limit_on_mult; auto. apply limit_on_const.
Qed.

Lemma limit_left_mult_const_r : forall f c a L,
  ⟦ lim a ⁻ ⟧ f = L -> ⟦ lim a ⁻ ⟧ (fun x => f x * c) = L * c.
Proof.
  intros f c a L H1.
  apply limit_left_eq with (f1 := f ⋅ (fun _ => c)).
  - exists 1. split; solve_R.
  - apply limit_left_mult; auto. apply limit_left_const.
Qed.

Lemma limit_right_mult_const_r : forall f c a L,
  ⟦ lim a ⁺ ⟧ f = L -> ⟦ lim a ⁺ ⟧ (fun x => f x * c) = L * c.
Proof.
  intros f c a L H1.
  apply limit_right_eq with (f1 := f ⋅ (fun _ => c)).
  - exists 1. split; solve_R.
  - apply limit_right_mult; auto. apply limit_right_const.
Qed.

Lemma limit_mult_const_r : forall f c a L,
  ⟦ lim a ⟧ f = L -> ⟦ lim a ⟧ (fun x => f x * c) = L * c.
Proof.
  intros f c a L H1.
  apply limit_eq with (f1 := f ⋅ (fun _ => c)).
  - exists 1. split; solve_R.
  - apply limit_mult; auto. apply limit_const.
Qed.

Lemma limit_on_mult_const_r : forall f c a D L,
  ⟦ lim a ⟧ f D = L -> ⟦ lim a ⟧ (fun x => f x * c) D = L * c.
Proof.
  intros f c a D L H1.
  apply limit_on_eq with (f1 := f ⋅ (fun _ => c)).
  - intros x H2. reflexivity.
  - apply limit_on_mult; auto. apply limit_on_const.
Qed.

Lemma limit_left_pow : forall f a L n,
  ⟦ lim a⁻ ⟧ f = L -> ⟦ lim a⁻ ⟧ (f ^ n) = L ^ n.
Proof.
  intros f a L n H1. induction n as [| n IH].
  - rewrite pow_O. replace ((fun x => f x ^ 0)) with (fun _ : ℝ => 1).
    2 : { extensionality x. rewrite pow_O. reflexivity. } apply limit_left_const; auto.
  - simpl. apply limit_left_mult; auto.
Qed.

Lemma limit_right_pow : forall f a L n,
  ⟦ lim a⁺ ⟧ f = L -> ⟦ lim a⁺ ⟧ (f ^ n) = L ^ n.
Proof.
  intros f a L n H1. induction n as [| n IH].
  - rewrite pow_O. replace ((fun x => f x ^ 0)) with (fun _ : ℝ => 1).
    2 : { extensionality x. rewrite pow_O. reflexivity. } apply limit_right_const; auto.
  - simpl. apply limit_right_mult; auto.
Qed.

Lemma limit_pow : forall f a L n,
  ⟦ lim a ⟧ f = L -> ⟦ lim a ⟧ (f ^ n) = L ^ n.
Proof.
  intros f a L n H1. apply limit_iff in H1 as [H2 H3].
  apply limit_iff; split; [ apply limit_left_pow | apply limit_right_pow ]; auto.
Qed.

Lemma limit_on_pow : forall f a D L n,
  ⟦ lim a ⟧ f D = L -> ⟦ lim a ⟧ (f ^ n) D = L ^ n.
Proof.
  intros f a D L n H1. induction n as [| n IH].
  - rewrite pow_O. replace ((fun x => f x ^ 0)) with (fun _ : ℝ => 1).
    2 : { extensionality x. rewrite pow_O. reflexivity. } apply limit_on_const; auto.
  - simpl. apply limit_on_mult; auto.
Qed.  

Lemma limit_left_inv : forall f a L,
  ⟦ lim a⁻ ⟧ f = L -> L <> 0 -> ⟦ lim a⁻ ⟧ (∕ f) = / L.
Proof.
  intros f a L H1 H2 ε H3. assert (|L| / 2 > 0) as H4 by solve_abs. assert (ε * |L|^2 / 2 > 0) as H5.
  { apply Rmult_lt_0_compat. apply pow2_gt_0 in H2. solve_abs. apply Rinv_pos; lra. }
  specialize (H1 (Rmin (|L| / 2) (ε * |L|^2 / 2)) ltac:(solve_min)) as [δ [H6 H7]].
  exists δ. split; try lra. intros x H8. specialize (H7 x H8). repeat rewrite <- Rdiv_1_l.
  apply lemma_1_22; auto.
Qed.

Lemma limit_right_inv : forall f a L,
  ⟦ lim a⁺ ⟧ f = L -> L <> 0 -> ⟦ lim a⁺ ⟧ (∕ f) = / L.
Proof.
  intros f a L H1 H2 ε H3. assert (|L| / 2 > 0) as H4 by solve_abs. assert (ε * |L|^2 / 2 > 0) as H5.
  { apply Rmult_lt_0_compat. apply pow2_gt_0 in H2. solve_abs. apply Rinv_pos; lra. }
  specialize (H1 (Rmin (|L| / 2) (ε * |L|^2 / 2)) ltac:(solve_min)) as [δ [H6 H7]].
  exists δ. split; try lra. intros x H8. specialize (H7 x H8). repeat rewrite <- Rdiv_1_l.
  apply lemma_1_22; auto.
Qed.

Lemma limit_inv : forall f a L,
  ⟦ lim a ⟧ f = L -> L <> 0 -> ⟦ lim a ⟧ (∕ f) = / L.
Proof.
  intros f a L H1 H2. apply limit_iff in H1 as [H3 H4].
  apply limit_iff; split; [ apply limit_left_inv | apply limit_right_inv ]; auto.
Qed.

Lemma limit_on_inv : forall f a D L,
  ⟦ lim a ⟧ f D = L -> L <> 0 -> ⟦ lim a ⟧ (∕ f) D = / L.
Proof.
  intros f a D L H1 H2 ε H3. assert (|L| / 2 > 0) as H4 by solve_abs. assert (ε * |L|^2 / 2 > 0) as H5.
  { apply Rmult_lt_0_compat. apply pow2_gt_0 in H2. solve_abs. apply Rinv_pos; lra. }
  specialize (H1 (Rmin (|L| / 2) (ε * |L|^2 / 2)) ltac:(solve_min)) as [δ [H6 H7]].
  exists δ. split; try lra. intros x H8 H9. specialize (H7 x H8 H9). repeat rewrite <- Rdiv_1_l.
  apply lemma_1_22; auto.
Qed.

Lemma limit_left_div : forall f1 f2 a L1 L2,
  ⟦ lim a⁻ ⟧ f1 = L1 -> ⟦ lim a⁻ ⟧ f2 = L2 -> L2 <> 0 -> ⟦ lim a⁻ ⟧ (f1 / f2) = L1 / L2.
Proof.
  intros f1 f2 a L1 L2 H1 H2 H3. replace (f1 / f2)%function with (f1 ⋅ (fun x => 1 / f2 x)).
  2 : { extensionality x. lra. }
  unfold Rdiv. apply limit_left_mult; auto. apply limit_left_inv; auto.
Qed.

Lemma limit_right_div : forall f1 f2 a L1 L2,
  ⟦ lim a⁺ ⟧ f1 = L1 -> ⟦ lim a⁺ ⟧ f2 = L2 -> L2 <> 0 -> ⟦ lim a⁺ ⟧ (f1 / f2) = L1 / L2.
Proof.
  intros f1 f2 a L1 L2 H1 H2 H3. replace (f1 / f2)%function with (f1 ⋅ (fun x => 1 / f2 x)).
  2 : { extensionality x. lra. }
  unfold Rdiv. apply limit_right_mult; auto. apply limit_right_inv; auto.
Qed.

Lemma limit_div : forall f1 f2 a L1 L2,
  ⟦ lim a ⟧ f1 = L1 -> ⟦ lim a ⟧ f2 = L2 -> L2 <> 0 -> ⟦ lim a ⟧ (f1 / f2) = L1 / L2.
Proof.
  intros f1 f2 a L1 L2 H1 H2 H3. apply limit_iff in H1 as [H4 H5], H2 as [H6 H7].
  apply limit_iff; split; [ apply limit_left_div | apply limit_right_div ]; auto.
Qed.

Lemma limit_on_div : forall f1 f2 a D L1 L2,
  ⟦ lim a ⟧ f1 D = L1 -> ⟦ lim a ⟧ f2 D = L2 -> L2 <> 0 -> ⟦ lim a ⟧ (f1 / f2) D = L1 / L2.
Proof.
  intros f1 f2 a D L1 L2 H1 H2 H3. replace (f1 / f2)%function with (f1 ⋅ (fun x => 1 / f2 x)).
  2 : { extensionality x. lra. }
  unfold Rdiv. apply limit_on_mult; auto. apply limit_on_inv; auto.
Qed.

Lemma sqrt_limit_helper_1 : forall x a,
  x >= 0 -> a >= 0 -> |√x - √a| = |x - a| / (√x + √a).  
Proof.
  intros x a H1 H2. pose proof Rtotal_order x a as [H3 | [H3 | H3]].
  - pose proof sqrt_lt_1_alt x a ltac:(lra) as H4. replace (|(√x - √a)|) with (√a - √x) by solve_abs.
    replace (|x - a|) with (a - x) by solve_abs. pose proof sqrt_lt_R0 a ltac:(lra) as H5. 
    pose proof sqrt_positivity x ltac:(lra) as H6. apply Rmult_eq_reg_r with (r := √x + √a); try nra.
    field_simplify; try nra. repeat rewrite pow2_sqrt; lra.
  - subst. solve_abs.
  - pose proof sqrt_lt_1_alt a x ltac:(lra) as H4. replace (|(√x - √a)|) with (√x - √a) by solve_abs.
    replace (|x - a|) with (x - a) by solve_abs. pose proof sqrt_lt_R0 x ltac:(lra) as H5. 
    pose proof sqrt_positivity a ltac:(lra) as H6. apply Rmult_eq_reg_r with (r := √x + √a); try nra.
    field_simplify; try nra. repeat rewrite pow2_sqrt; lra.
Qed.

Lemma sqrt_limit_helper_2 : forall x a,
  a >= 0 -> |x - a| < a / 2 -> √x + √a > √(a/2) + √a.
Proof.
  intros x a H1 H2. pose proof Rtotal_order x a as [H3 | [H3 | H3]].
  - replace (|x - a|) with (a - x) in H2 by solve_abs. assert (a / 2 < x) as H4 by lra.
    pose proof sqrt_lt_1_alt (a/2) x ltac:(lra) as H5. lra.
  - subst. pose proof sqrt_lt_1_alt (a/2) a ltac:(solve_R) as H5. lra.
  - pose proof sqrt_lt_1_alt (a/2) x ltac:(lra) as H4. lra.
Qed.

Lemma limit_sqrt : forall a,
  ⟦ lim a ⟧ (fun x => √x) = √a.
Proof.
  intros a ε H1. assert (a <= 0 \/ a > 0) as [H2 | H2] by solve_R.
  - exists (ε^2). split. nra. intros x H3. assert (x < a \/ x > a) as [H4 | H4] by solve_abs.
    -- repeat rewrite sqrt_neg_0; solve_abs.
    -- rewrite (sqrt_neg_0 a); try lra. replace (|x - a|) with (x - a) in H3 by solve_abs.
       assert (x < ε ^ 2) as H5 by nra. pose proof sqrt_pos x as H6. replace (|(√x - 0)|) with (√x) by solve_abs.
       apply Rlt_pow_base with (n := 2%nat); try lra; try lia. assert (x <= 0 \/ x > 0) as [H7 | H7] by solve_R.
       apply sqrt_neg_0 in H7. rewrite H7. lra. rewrite pow2_sqrt; lra.
  - set (δ := Rmin (a / 2) ((√(a/2) + √a) * ε)). exists δ. split.
    -- unfold δ. pose proof sqrt_lt_R0 a ltac:(lra) as H3.
       pose proof sqrt_lt_R0 (a / 2) ltac:(apply Rdiv_pos_pos; lra) as H4. solve_min.
    -- intros x H3. assert (|x - a| < a / 2) as H4 by (unfold δ in *; solve_R).
       assert (|x - a| < (√(a / 2) + √a) * ε) as H5 by (unfold δ in *; solve_R).
       assert (x < 0 \/ x >= 0) as [H6 | H6] by solve_R.
       * rewrite sqrt_neg_0; try lra. solve_abs.
       * pose proof sqrt_limit_helper_2 x a ltac:(lra) ltac:(lra) as H7.
         rewrite sqrt_limit_helper_1; try lra. apply Rmult_lt_reg_r with (r := √x + √a); try nra.
         field_simplify; nra.
Qed.

Lemma limit_left_sqrt : forall a,
  ⟦ lim a⁻ ⟧ (fun x => √x) = √a.
Proof. intros a. apply limit_iff. apply limit_sqrt. Qed.

Lemma limit_right_sqrt : forall a,
  ⟦ lim a⁺ ⟧ (fun x => √x) = √a.
Proof. intros a. apply limit_iff. apply limit_sqrt. Qed.

Lemma limit_on_sqrt : forall a D,
  ⟦ lim a ⟧ (fun x => √x) D = √a.
Proof. intros a D. apply limit_imp_limit_on; apply limit_sqrt. Qed.

Lemma limit_comp : ∀ (f g : ℝ → ℝ) (a b l : ℝ),
  ⟦ lim a ⟧ g = b ->
  ⟦ lim b ⟧ f = l ->
  (∃ δ : ℝ, δ > 0 ∧ ∀ x, 0 < |x - a| < δ -> g x ≠ b) ->
  ⟦ lim a ⟧ (λ x, f (g x)) = l.
Proof.
  intros f g a b l H1 H2 H3 ε H4.
  specialize (H2 ε H4) as [δ1 [H5 H6]].
  specialize (H1 δ1 H5) as [δ2 [H7 H8]].
  destruct H3 as [δ3 [H9 H10]].
  set (δ := Rmin δ2 δ3).
  exists δ. split; [unfold δ; solve_min |].
  intros x H12.
  specialize (H8 x ltac:(unfold δ in *; solve_R)).
  specialize (H6 (g x)).
  assert (H13: 0 < |g x - b| < δ1).
  { specialize (H10 x ltac:(unfold δ in *; solve_R)). solve_R. }
  auto.
Qed.

Lemma limit_squeeze : ∀ f1 f2 f3 a b c L,
  a < b -> c ∈ (a, b) -> 
  ⟦ lim c ⟧ f1 = L -> ⟦ lim c ⟧ f3 = L -> 
  (∀ x, x ∈ ((a, c) ⋃ (c, b)) -> f1 x <= f2 x <= f3 x) -> 
  ⟦ lim c ⟧ f2 = L.
Proof.
  intros f1 f2 f3 a b c L H1 H2 H3 H4 H5 ε H6. specialize (H3 ε H6) as [δ1 [H7 H8]].
  specialize (H4 ε H6) as [δ2 [H9 H10]]. set (δ := Rmin δ1 (Rmin δ2 (Rmin (b - c) (c - a)))).
  assert (δ > 0) as H11 by (unfold δ; solve_R). exists δ. split; auto. intros x H12. specialize (H8 x ltac:(unfold δ in *; solve_R)).
  specialize (H10 x ltac:(unfold δ in *; solve_R)).
  assert (x ∈ ((a, c) ⋃ (c, b))) as H13. {
    assert (x < c \/ x > c) as [H14 | H14] by solve_R.
    - left. unfold δ in *; solve_R.
    - right. unfold δ in *; solve_R.
  }
  specialize (H5 x H13). assert (f1 x <= f2 x <= f3 x) as H15 by auto. solve_R.
Qed.

Lemma limit_right_squeeze : forall f1 f2 f3 c b L,
  c < b -> ⟦ lim c⁺ ⟧ f1 = L -> ⟦ lim c⁺ ⟧ f3 = L -> (forall x, x ∈ (c, b) -> f1 x <= f2 x <= f3 x) -> ⟦ lim c⁺ ⟧ f2 = L.
Proof.
  intros f1 f2 f3 b c L H1 H2 H3 H4 ε H5. specialize (H3 ε H5) as [δ1 [H6 H7]].
  specialize (H2 ε H5) as [δ2 [H8 H9]]. set (δ := Rmin δ1 (Rmin δ2 (c - b))). unfold Ensembles.In in *.
  assert (δ > 0) as H10 by (unfold δ; solve_R). exists δ. split; auto. intros x H11. specialize (H7 x ltac:(unfold δ in *; solve_R)).
  specialize (H9 x ltac:(unfold δ in *; solve_R)).
  specialize (H4 x ltac:(unfold δ in *; solve_R)). 
  solve_R.
Qed.

Lemma limit_left_squeeze : forall f1 f2 f3 a c L,
  a < c -> ⟦ lim c⁻ ⟧ f1 = L -> ⟦ lim c⁻ ⟧ f3 = L -> (forall x, x ∈ (a, c) -> f1 x <= f2 x <= f3 x) -> ⟦ lim c⁻ ⟧ f2 = L.
Proof.
  intros f1 f2 f3 a c L H1 H2 H3 H4 ε H5. specialize (H3 ε H5) as [δ1 [H6 H7]].
  specialize (H2 ε H5) as [δ2 [H8 H9]]. set (δ := Rmin δ1 (Rmin δ2 (c - a))). unfold Ensembles.In in *.
  assert (δ > 0) as H10 by (unfold δ; solve_R). exists δ. split; auto. intros x H11. specialize (H7 x ltac:(unfold δ in *; solve_R)).
  specialize (H9 x ltac:(unfold δ in *; solve_R)).
  specialize (H4 x ltac:(unfold δ in *; solve_R)). 
  solve_R.
Qed.

Lemma limit_neq_neighborhood : forall f a L x,
  ⟦ lim a ⟧ f = L -> L <> x -> 
  exists δ, δ > 0 /\ forall y, 0 < |y - a| < δ -> f y <> x.
Proof.
  intros f a L x H1 H2.
  specialize (H1 (|L - x| / 2) ltac:(solve_abs)).
  destruct H1 as [δ [H4 H5]].
  exists δ; split; auto.
  intros y H6 H7. specialize (H5 y H6). rewrite H7 in H5. solve_abs.
Qed.

Lemma limit_shift : forall f a c L,
  ⟦ lim a ⟧ (fun x => f (x + c)) = L <-> ⟦ lim (a + c) ⟧ f = L.
Proof.
   intros f a c L. split.
  - intros H1 ε H2.
    specialize (H1 ε H2) as [δ [H3 H4]].
    exists δ; split; auto.
    intros y H5.
    replace y with ((y - c) + c) by lra.
    apply H4.
    replace (y - c - a) with (y - (a + c)) by lra. auto.
  - intros H1 ε H2.
    specialize (H1 ε H2) as [δ [H3 H4]].
    exists δ; split; auto.
    intros x H5.
    apply H4.
    replace (x + c - (a + c)) with (x - a) by lra. auto.
Qed.

Lemma limit_plus_const : forall f a L C,
  ⟦ lim a ⟧ f = L <-> ⟦ lim a ⟧ (f + (fun _ => C)) = L + C.
Proof.
  intros f a L C. split; intro H.
  - apply limit_plus; [exact H | apply limit_const].
  - replace f with (((f + (fun _ => C))%function - (fun _ => C))%function) by (extensionality x; lra).
    replace L with (L + C - C) by lra. apply limit_minus; [exact H | apply limit_const].
Qed.

Lemma limit_minus_const : forall f a L C,
  ⟦ lim a ⟧ f = L <-> ⟦ lim a ⟧ (f - (fun _ => C)) = L - C.
Proof.
  intros f a L C. split; intro H.
  - apply limit_minus; [exact H | apply limit_const].
  - replace f with (((f - (fun _ => C))%function + (fun _ => C))%function) by (extensionality x; lra).
    replace L with (L - C + C) by lra. apply limit_plus; [exact H | apply limit_const].
Qed.

Lemma limit_continuous_comp :
  forall (f g : R -> R) (a L : R),
    ⟦ lim a ⟧ g = L ->
    ⟦ lim L ⟧ f = f L ->
    ⟦ lim a ⟧ (fun x => f (g x)) = f L.
Proof.
  intros f g a L H1 H2 ε H3. specialize (H2 ε H3) as [δ1 [H4 H5]].
  specialize (H1 δ1 H4) as [δ2 [H6 H7]]. exists δ2. split; auto. intros x H8.
  specialize (H7 x H8). specialize (H5 (g x)).
  pose proof classic (g x = L) as [H9 | H9].
  - rewrite H9. solve_R.
  - specialize (H5 ltac:(solve_R)). auto.
Qed.

Lemma limit_right_continuous_comp :
  forall (f g : R -> R) (a L : R),
    ⟦ lim a⁺ ⟧ g = L ->
    ⟦ lim L ⟧ f = f L ->
    ⟦ lim a⁺ ⟧ (fun x => f (g x)) = f L.
Proof.
  intros f g a L H1 H2 ε H3. specialize (H2 ε H3) as [δ1 [H4 H5]].
  specialize (H1 δ1 H4) as [δ2 [H6 H7]]. exists δ2. split; auto. intros x H8.
  specialize (H7 x H8). specialize (H5 (g x)).
  pose proof classic (g x = L) as [H9 | H9].
  - rewrite H9. solve_R.
  - specialize (H5 ltac:(solve_R)). auto.
Qed.

Lemma limit_left_continuous_comp :
  forall (f g : R -> R) (a L : R),
    ⟦ lim a⁻ ⟧ g = L ->
    ⟦ lim L ⟧ f = f L ->
    ⟦ lim a⁻ ⟧ (fun x => f (g x)) = f L.
Proof.
  intros f g a L H1 H2 ε H3. specialize (H2 ε H3) as [δ1 [H4 H5]].
  specialize (H1 δ1 H4) as [δ2 [H6 H7]]. exists δ2. split; auto. intros x H8.
  specialize (H7 x H8). specialize (H5 (g x)).
  pose proof classic (g x = L) as [H9 | H9].
  - rewrite H9. solve_R.
  - specialize (H5 ltac:(solve_R)). auto.
Qed.

Lemma limit_sqrt_f_x : forall f a L,
  ⟦ lim a ⟧ f = L -> L >= 0 -> ⟦ lim a ⟧ (fun x => √(f x)) = √L.
Proof.
  intros f a L H1 H2. apply limit_continuous_comp; auto. apply limit_sqrt.
Qed.

Lemma limit_right_sqrt_f_x : forall f a L,
  ⟦ lim a⁺ ⟧ f = L -> L >= 0 -> ⟦ lim a⁺ ⟧ (fun x => √(f x)) = √L.
Proof.
  intros f a L H1 H2. apply limit_right_continuous_comp; auto. apply limit_sqrt.
Qed.

Lemma limit_left_sqrt_f_x : forall f a L,
  ⟦ lim a⁻ ⟧ f = L -> L >= 0 -> ⟦ lim a⁻ ⟧ (fun x => √(f x)) = √L.
Proof.
  intros f a L H1 H2. apply limit_left_continuous_comp; auto. apply limit_sqrt.
Qed.

Lemma limit_pos_neighborhood : forall f a L,
  ⟦ lim a ⟧ f = L -> L > 0 ->
  exists δ, δ > 0 /\ forall x, 0 < |x - a| < δ -> f x > 0.
Proof.
  intros f a L H1 H2.
  specialize (H1 (L/2) ltac:(lra)) as [δ [H3 H4]].
  exists δ. split; auto.
  intros x H5. specialize (H4 x H5). solve_R.
Qed.

Lemma limit_neg_neighborhood : forall f a L,
  ⟦ lim a ⟧ f = L -> L < 0 ->
  exists δ, δ > 0 /\ forall x, 0 < |x - a| < δ -> f x < 0.
Proof.
  intros f a L H1 H2.
  specialize (H1 (-L/2) ltac:(lra)) as [δ [H3 H4]].
  exists δ. split; auto.
  intros x H5. specialize (H4 x H5). solve_R.
Qed.

Ltac solve_lim :=
  try solve_R;
  match goal with
  | [ |- ⟦ lim ?a ⟧ ?f = ?rhs ] =>
      let L_eval := eval cbv beta in (f a) in
      let L := eval simpl in L_eval in
      let H := fresh "H" in
      assert (⟦ lim a ⟧ f = L) as H by
        (repeat (first [
             apply limit_div 
           | apply limit_pow 
           | apply limit_mult 
           | apply limit_inv 
           | apply limit_plus 
           | apply limit_minus 
           | apply limit_sqrt 
           | apply limit_id 
           | apply limit_const 
           | solve_R 
           ])); 
      apply (limit_subst f a L rhs); [solve_R | exact H]
  end.