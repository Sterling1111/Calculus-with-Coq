From Lib Require Import Imports Sequence Sets Reals_util Notations Functions.
Import SetNotations IntervalNotations.

Open Scope R_scope.
Open Scope interval_scope.

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

  Delimit Scope limit_scope with l. 

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

End LimitNotations.

Import LimitNotations.

Open Scope limit_scope.

Definition circle (a b r : ℝ) : Ensemble (ℝ * ℝ) :=
  fun p => let (x, y) := p in
  (x - a)^2 + (y - b)^2 = r^2.

Lemma limit_imp_limit_on : forall f L D a,
  ⟦ lim a ⟧ f = L -> ⟦ lim a ⟧ f D = L.
Proof.
  intros f L D a H1. intros ε H2. specialize (H1 ε H2) as [δ [H3 H4]]. exists δ; split; auto.
Qed.

Lemma left_right_iff : forall f a L,
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

Lemma lemma_1_20 : forall x x0 y y0 ε,
  |x - x0| < ε / 2 -> |y - y0| < ε / 2 -> |(x + y) - (x0 + y0)| < ε /\ |(x - y) - (x0 - y0)| < ε.
Proof.
  solve_abs.
Qed.

Lemma lemma_1_21 : forall x x0 y y0 ε,
  |x - x0| < Rmin (ε / (2 * (|y0| + 1))) 1 -> |y - y0| < ε / (2 * (|x0| + 1)) -> |x * y - x0 * y0| < ε.
Proof.
  intros x x0 y y0 ε H1 H2. assert (H3 : (Rabs (x - x0)) < 1). { apply Rlt_gt in H1. apply Rmin_Rgt_l in H1. lra. }
  assert (H4 : Rabs x - Rabs x0 < 1). { pose proof Rabs_triang_inv x x0. lra. }
  assert (H5 : Rabs (y - y0) >= 0) by (apply Rle_ge; apply Rabs_pos).
  assert (H6 : Rabs x0 >= 0) by (apply Rle_ge; apply Rabs_pos).
  assert (H7 : ε > 0).
  { 
    pose proof Rtotal_order ε 0 as [H7 | [H7 | H7]].
    - assert (H8 : ε / (2 * (Rabs x0 + 1)) < 0). { apply Rdiv_neg_pos. lra. lra. } lra.
    - nra.
    - apply H7.
  }
  assert (H8 : Rabs x < 1 + Rabs x0) by lra. replace (x * y - x0 * y0) with (x * (y - y0) + y0 * (x - x0)) by lra.
  assert (H9 : Rabs (x * (y - y0) + y0 * (x - x0)) <= Rabs x * Rabs (y - y0) + Rabs y0 * Rabs (x - x0)) by solve_abs.
  assert (H10 : (1 + Rabs x0) * (ε / (2 * (Rabs x0 + 1))) = ε / 2). { field; try unfold Rabs; try destruct Rcase_abs; try nra. }
  assert (H11 : forall x, x >= 0 -> x / (2 * (x + 1)) < 1 / 2).
  {
    intros x1 H11. apply Rmult_lt_reg_l with (r := 2). lra. unfold Rdiv.
    replace (2 * (1 * / 2)) with (1) by lra. replace (2 * (x1 * / (2 * (x1 + 1)))) with ((x1) * (2 * / (2 * (x1 + 1)))) by lra.
    rewrite Rinv_mult. replace (2 * (/ 2 * / (x1 + 1))) with (2 * / 2 * / (x1 + 1)) by nra. rewrite Rinv_r. 2 : lra.
    rewrite Rmult_1_l. rewrite <- Rdiv_def. apply Rdiv_lt_1. lra. lra.
  }
  assert (H12 : (Rabs y0 * (ε / (2 * ((Rabs y0) + 1)))) < ε / 2). 
  { 
    replace (Rabs y0 * (ε / (2 * (Rabs y0 + 1)))) with (ε * (Rabs y0 * / (2 * (Rabs y0 + 1)))) by lra.
    pose proof H11 (Rabs y0) as H12. unfold Rdiv. apply Rmult_lt_compat_l. lra. unfold Rdiv in H12. rewrite Rmult_1_l in H12.
    apply H12. apply Rle_ge. apply Rabs_pos.
  }
  replace (ε) with (ε / 2 + ε / 2) by lra. 
  assert (H13 : Rabs x * Rabs (y - y0) < ((1 + Rabs x0) * (ε / (2 * (Rabs x0 + 1))))) by nra.
  assert (H14 : Rabs (x - x0) < (ε / (2 * (Rabs y0 + 1)))). { apply Rlt_gt in H1. apply Rmin_Rgt_l in H1. lra. }
  assert (H15 : Rabs y0 >= 0) by (apply Rle_ge; apply Rabs_pos).
  assert (H16 : Rabs (x - x0) >= 0) by (apply Rle_ge; apply Rabs_pos).
  assert (H17 : Rabs y0 * Rabs (x - x0) <= (Rabs y0 * (ε / (2 * ((Rabs y0 + 1)))))) by nra.
  nra.
Qed.

Lemma lemma_1_22 : forall y y0 ε,
  y0 <> 0 -> |y - y0| < Rmin (|y0| / 2) ((ε * |y0|^2) / 2) -> y <> 0 /\ |1 / y - 1 / y0| < ε.
Proof.
  intros y y0 eps H1 H2. assert (H3 : y <> 0).
  - assert (H4 : Rabs (y - y0) < Rabs (y0 / 2)). { apply Rlt_gt in H2. apply Rmin_Rgt_l in H2. solve_abs. } solve_abs.
  - split.
    -- apply H3.
    -- assert (H4 : Rabs (y - y0) < Rabs (y0 / 2)). { apply Rlt_gt in H2. apply Rmin_Rgt_l in H2. solve_abs. }
       assert (H5 : Rabs (y - y0) < (eps * (Rabs y0)^2) / 2). { apply Rlt_gt in H2. apply Rmin_Rgt_l in H2. lra. }
       assert (H6 : Rabs y > Rabs y0 / 2) by solve_abs.
       assert (H7 : Rabs y > 0) by solve_abs. assert (H8 : Rabs y0 > 0) by solve_abs.
       assert (H9 : forall a b : R, a > 0 -> b > 0 -> a > b / 2 -> 1 / a < 2 / b).
       { 
          intros a b H9 H10 H11. apply Rmult_lt_reg_r with (r := a). lra. replace (1 / a * a) with 1 by (field; lra).
          apply Rmult_lt_reg_r with (r := b). lra. replace (2 / b * a * b) with (2 * a) by (field; lra). lra.
       }
       assert (H10 : 1 / Rabs y < 2 / Rabs y0). { apply H9. apply H7. apply H8. apply H6. } clear H9.
       replace (1 / y - 1 / y0) with ((y0 - y) / (y * y0)) by (field; lra). 
       unfold Rdiv. rewrite Rabs_mult. rewrite Rabs_inv. rewrite <- Rdiv_def. rewrite Rabs_mult.
       rewrite Rabs_minus_sym. assert (H11 : 2 * Rabs (y - y0) < eps * Rabs y0 ^ 2). { lra. }
       assert (H12 : (2 * Rabs (y - y0)) / (Rabs y0 ^ 2) < eps).
       { apply Rmult_lt_reg_r with (r := Rabs y0 ^ 2). nra. apply Rmult_lt_reg_r with (r := / 2). nra.
          replace (2 * Rabs (y - y0) / (Rabs y0 ^ 2) * Rabs y0 ^2 * / 2) with 
          (2 * Rabs (y - y0) * / 2) by (field; lra). lra.
       }
       replace (2 * Rabs (y - y0) / Rabs y0 ^ 2) with (Rabs (y - y0) / ((Rabs y0 / 2) * Rabs y0)) in H12 by (field; nra).
       assert (H13 : (Rabs y0 / 2 * Rabs y0) < Rabs y * Rabs y0) by nra. 
       assert (H14 : forall a b c, a > 0 -> b > 0 -> c >= 0 -> a > b -> c / a <= c / b).
       {
          intros a b c H14 H15 H16 H17. apply Rmult_le_reg_r with (r := a). lra.
          replace (c / a * a) with c by (field; lra). apply Rmult_le_reg_r with (r := b). lra.
          replace (c / b * a * b) with (c * a) by (field; lra). nra.
       }
       assert (H15 : Rabs (y - y0) / (Rabs y0 / 2 * Rabs y0) >= Rabs (y - y0) / (Rabs y * Rabs y0)). 
       { apply Rle_ge. apply H14. nra. nra. apply Rle_ge. apply Rabs_pos. nra. }
       nra.
Qed. 

Module Function_Notations.

  Delimit Scope function_scope with f.

  Notation "f ∘ g" := (compose f g) (at level 40, left associativity) : function_scope.
  Notation "f + g" := (fun x : ℝ => f x + g x) (at level 50, left associativity) : function_scope.
  Notation "f - g" := (fun x : ℝ => f x - g x) (at level 50, left associativity) : function_scope.
  Notation "- f" := (fun x : ℝ => - f x) (at level 35) : function_scope.
  Notation "f ∙ g" := (fun x : ℝ => f x * g x) (at level 40, left associativity) : function_scope. 
  Notation "c * f" := (fun x : ℝ => c * f x) (at level 40, left associativity) : function_scope. 
  Notation "f / g" := (fun x : ℝ => f x / g x) (at level 40, left associativity) : function_scope.
  Notation "f ^ n" := (fun x : ℝ => (f x) ^ n) (at level 30, right associativity) : function_scope.
  Notation "∕ f" := (fun x : ℝ => 1 / f x) (at level 40, left associativity) : function_scope.

End Function_Notations.

Import Function_Notations.

Lemma limit_of_function_unique : forall f a L1 L2,
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

Lemma left_limit_of_function_unique : forall f a L1 L2,
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

Lemma right_limit_of_function_unique : forall f a L1 L2,
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

Lemma left_limit_plus : forall f1 f2 a L1 L2,
  ⟦ lim a⁻ ⟧ f1 = L1 -> ⟦ lim a⁻ ⟧ f2 = L2 -> ⟦ lim a⁻ ⟧ (f1 + f2) = (L1 + L2).
Proof.
  intros f1 f2 a L1 L2 H1 H2 ε H3. specialize (H1 (ε / 2) ltac:(lra)) as [δ1 [H4 H5]].
  specialize (H2 (ε / 2) ltac:(lra)) as [δ2 [H6 H7]]. set (δ := Rmin δ1 δ2).
  assert (δ > 0) as H8 by (unfold δ; solve_min). exists δ. split; try lra.
  intros x H9. specialize (H5 x ltac:(unfold δ in *; solve_R)). specialize (H7 x ltac:(unfold δ in *; solve_R)).
  solve_R.
Qed.

Lemma right_limit_plus : forall f1 f2 a L1 L2,
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
  intros f1 f2 a L1 L2 H1 H2. apply left_right_iff in H1 as [H3 H4], H2 as [H5 H6].
  apply left_right_iff; split; [ apply left_limit_plus | apply right_limit_plus ]; auto.
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

Lemma left_limit_const : forall a c,
  ⟦ lim a⁻ ⟧ (fun _ => c) = c.
Proof.
  intros a c ε H1. exists 1; split; solve_abs.
Qed.

Lemma right_limit_const : forall a c,
  ⟦ lim a⁺ ⟧ (fun _ => c) = c.
Proof.
  intros a c ε H1. exists 1; split; solve_abs.
Qed.

Lemma limit_const : forall a c,
  ⟦ lim a ⟧ (fun _ => c) = c.
Proof.
  intros a c ε H1. exists 1; split; solve_abs.
Qed.

Lemma limit_on_const : forall a D c,
  ⟦ lim a ⟧ (fun _ => c) D = c.
Proof.
  intros a D c ε H1. exists 1; split; solve_abs.
Qed.

Lemma  left_limit_id : forall a,
  ⟦ lim a⁻ ⟧ (fun x => x) = a.
Proof.
  intros a ε H1. exists ε. split; solve_abs.
Qed.

Lemma right_limit_id : forall a,
  ⟦ lim a⁺ ⟧ (fun x => x) = a.
Proof.
  intros a ε H1. exists ε. split; solve_abs.
Qed.

Lemma limit_id : forall a,
  ⟦ lim a ⟧ (fun x => x) = a.
Proof.
  intros a ε H1. exists ε. split; solve_abs.
Qed.

Lemma left_limit_minus : forall f1 f2 a L1 L2,
  ⟦ lim a⁻ ⟧ f1 = L1 -> ⟦ lim a⁻ ⟧ f2 = L2 -> ⟦ lim a⁻ ⟧ (f1 - f2) = (L1 - L2).
Proof.
  intros f1 f2 a L1 L2 H1 H2. unfold Rminus. apply left_limit_plus; auto.
  intros ε H3. specialize (H2 ε H3) as [δ [H4 H5]].
  exists δ. split; auto. intros x H6. apply H5 in H6. solve_abs.
Qed.

Lemma right_limit_minus : forall f1 f2 a L1 L2,
  ⟦ lim a⁺ ⟧ f1 = L1 -> ⟦ lim a⁺ ⟧ f2 = L2 -> ⟦ lim a⁺ ⟧ (f1 - f2) = (L1 - L2).
Proof.
  intros f1 f2 a L1 L2 H1 H2. unfold Rminus. apply right_limit_plus; auto.
  intros ε H3. specialize (H2 ε H3) as [δ [H4 H5]].
  exists δ. split; auto. intros x H6. apply H5 in H6. solve_abs.
Qed.

Lemma limit_minus : forall f1 f2 a L1 L2,
  ⟦ lim a ⟧ f1 = L1 -> ⟦ lim a ⟧ f2 = L2 -> ⟦ lim a ⟧ (f1 - f2) = (L1 - L2).
Proof.
  intros f1 f2 a L1 L2 H1 H2. apply left_right_iff in H1 as [H3 H4], H2 as [H5 H6].
  apply left_right_iff; split; [ apply left_limit_minus | apply right_limit_minus ]; auto.
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

Lemma left_limit_mult : forall f1 f2 a L1 L2,
  ⟦ lim a⁻ ⟧ f1 = L1 -> ⟦ lim a⁻ ⟧ f2 = L2 -> ⟦ lim a⁻ ⟧ (f1 ∙ f2) = L1 * L2.
Proof.
  intros f1 f2 a L1 L2 H1 H2 ε H3. assert (ε / (2 * ((|L2|) + 1)) > 0 /\ ε / (2 * ((|L1|) + 1)) > 0) as [H4 H5].
  { split; apply Rdiv_pos_pos; solve_abs. }
  specialize (H1 (Rmin (ε / (2 * ((|L2|) + 1))) 1) ltac:(solve_min)) as [δ1 [H6 H7]].
  specialize (H2 (ε / (2 * ((|L1|) + 1))) ltac:(solve_min)) as [δ2 [H8 H9]].
  set (δ := Rmin δ1 δ2). assert (δ > 0) as H10 by (unfold δ; solve_min). exists δ. split; try lra.
  intros x H11. assert (0 < a - x < δ1 /\ 0 < a - x < δ2) as [H12 H13] by (unfold δ in H11; solve_min).
  specialize (H7 x H12). specialize (H9 x H13). apply lemma_1_21; auto.
Qed.

Lemma right_limit_mult : forall f1 f2 a L1 L2,
  ⟦ lim a⁺ ⟧ f1 = L1 -> ⟦ lim a⁺ ⟧ f2 = L2 -> ⟦ lim a⁺ ⟧ (f1 ∙ f2) = L1 * L2.
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
  ⟦ lim a ⟧ f1 = L1 -> ⟦ lim a ⟧ f2 = L2 -> ⟦ lim a ⟧ (f1 ∙ f2) = L1 * L2.
Proof.
  intros f1 f2 a L1 L2 H1 H2. apply left_right_iff in H1 as [H3 H4], H2 as [H5 H6].
  apply left_right_iff; split; [ apply left_limit_mult | apply right_limit_mult ]; auto.
Qed.

Lemma limit_on_mult : forall f1 f2 a D L1 L2,
  ⟦ lim a ⟧ f1 D = L1 -> ⟦ lim a ⟧ f2 D = L2 -> ⟦ lim a ⟧ (f1 ∙ f2) D = L1 * L2.
Proof.
  intros f1 f2 a D L1 L2 H1 H2 ε H3. assert (ε / (2 * ((|L2|) + 1)) > 0 /\ ε / (2 * ((|L1|) + 1)) > 0) as [H4 H5].
  { split; apply Rdiv_pos_pos; solve_abs. }
  specialize (H1 (Rmin (ε / (2 * ((|L2|) + 1))) 1) ltac:(solve_min)) as [δ1 [H6 H7]].
  specialize (H2 (Rmin (ε / (2 * ((|L1|) + 1))) 1) ltac:(solve_min)) as [δ2 [H8 H9]].
  set (δ := Rmin δ1 δ2). assert (δ > 0) as H10 by (unfold δ; solve_min). exists δ. split; try lra.
  intros x H11 H12. assert (0 < |x - a| < δ1 /\ 0 < |x - a| < δ2) as [H13 H14] by (unfold δ in *; solve_R).
  specialize (H7 x H11 H13). specialize (H9 x H11 H14). apply lemma_1_21; auto. solve_R.
Qed.

Lemma limit_on_eq_f : forall f1 f2 D L x,
  ⟦ lim x ⟧ f1 D = L -> (forall x, x ∈ D -> f1 x = f2 x) -> ⟦ lim x ⟧ f2 D = L.
Proof.
  intros f1 f2 D L x H1 H2 ε H3. specialize (H1 ε H3) as [δ [H1 H4]].
  exists δ; split; auto. intros x0 H5 H6. specialize (H4 x0 H5 H6).
  rewrite <- H2; solve_R.
Qed.

Lemma left_limit_inv : forall f a L,
  ⟦ lim a⁻ ⟧ f = L -> L <> 0 -> ⟦ lim a⁻ ⟧ (∕ f) = / L.
Proof.
  intros f a L H1 H2 ε H3. assert (|L| / 2 > 0) as H4 by solve_abs. assert (ε * |L|^2 / 2 > 0) as H5.
  { apply Rmult_lt_0_compat. apply pow2_gt_0 in H2. solve_abs. apply Rinv_pos; lra. }
  specialize (H1 (Rmin (|L| / 2) (ε * |L|^2 / 2)) ltac:(solve_min)) as [δ [H6 H7]].
  exists δ. split; try lra. intros x H8. specialize (H7 x H8). repeat rewrite <- Rdiv_1_l.
  apply lemma_1_22; auto.
Qed.

Lemma right_limit_inv : forall f a L,
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
  intros f a L H1 H2. apply left_right_iff in H1 as [H3 H4].
  apply left_right_iff; split; [ apply left_limit_inv | apply right_limit_inv ]; auto.
Qed.

Lemma left_limit_div : forall f1 f2 a L1 L2,
  ⟦ lim a⁻ ⟧ f1 = L1 -> ⟦ lim a⁻ ⟧ f2 = L2 -> L2 <> 0 -> ⟦ lim a⁻ ⟧ (f1 / f2) = L1 / L2.
Proof.
  intros f1 f2 a L1 L2 H1 H2 H3. replace (f1 / f2)%function with (f1 ∙ (fun x => 1 / f2 x)).
  2 : { extensionality x. lra. }
  unfold Rdiv. apply left_limit_mult; auto. apply left_limit_inv; auto.
Qed.

Lemma right_limit_div : forall f1 f2 a L1 L2,
  ⟦ lim a⁺ ⟧ f1 = L1 -> ⟦ lim a⁺ ⟧ f2 = L2 -> L2 <> 0 -> ⟦ lim a⁺ ⟧ (f1 / f2) = L1 / L2.
Proof.
  intros f1 f2 a L1 L2 H1 H2 H3. replace (f1 / f2)%function with (f1 ∙ (fun x => 1 / f2 x)).
  2 : { extensionality x. lra. }
  unfold Rdiv. apply right_limit_mult; auto. apply right_limit_inv; auto.
Qed.

Lemma limit_div : forall f1 f2 a L1 L2,
  ⟦ lim a ⟧ f1 = L1 -> ⟦ lim a ⟧ f2 = L2 -> L2 <> 0 -> ⟦ lim a ⟧ (f1 / f2) = L1 / L2.
Proof.
  intros f1 f2 a L1 L2 H1 H2 H3. apply left_right_iff in H1 as [H4 H5], H2 as [H6 H7].
  apply left_right_iff; split; [ apply left_limit_div | apply right_limit_div ]; auto.
Qed.

Lemma left_limit_pow : forall f a L n,
  ⟦ lim a⁻ ⟧ f = L -> ⟦ lim a⁻ ⟧ (f ^ n) = L ^ n.
Proof.
  intros f a L n H1. induction n as [| n IH].
  - rewrite pow_O. replace ((fun x => f x ^ 0)) with (fun _ : ℝ => 1).
    2 : { extensionality x. rewrite pow_O. reflexivity. } apply left_limit_const; auto.
  - simpl. apply left_limit_mult; auto.
Qed.

Lemma right_limit_pow : forall f a L n,
  ⟦ lim a⁺ ⟧ f = L -> ⟦ lim a⁺ ⟧ (f ^ n) = L ^ n.
Proof.
  intros f a L n H1. induction n as [| n IH].
  - rewrite pow_O. replace ((fun x => f x ^ 0)) with (fun _ : ℝ => 1).
    2 : { extensionality x. rewrite pow_O. reflexivity. } apply right_limit_const; auto.
  - simpl. apply right_limit_mult; auto.
Qed.

Lemma limit_pow : forall f a L n,
  ⟦ lim a ⟧ f = L -> ⟦ lim a ⟧ (f ^ n) = L ^ n.
Proof.
  intros f a L n H1. apply left_right_iff in H1 as [H2 H3].
  apply left_right_iff; split; [ apply left_limit_pow | apply right_limit_pow ]; auto.
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

Lemma limit_sqrt_x : forall a,
  ⟦ lim a ⟧ (fun x => √x) = √a.
Proof.
  intros a ε H1. assert (a <= 0 \/ a > 0) as [H2 | H2] by lra.
  - exists (ε^2). split. nra. intros x H3. assert (x < a \/ x > a) as [H4 | H4] by solve_abs.
    -- repeat rewrite sqrt_neg_0; solve_abs.
    -- rewrite (sqrt_neg_0 a); try lra. replace (|x - a|) with (x - a) in H3 by solve_abs.
       assert (x < ε ^ 2) as H5 by nra. pose proof sqrt_pos x as H6. replace (|(√x - 0)|) with (√x) by solve_abs.
       apply Rlt_pow_base with (n := 2%nat); try lra; try lia. assert (x <= 0 \/ x > 0) as [H7 | H7] by lra.
       apply sqrt_neg_0 in H7. rewrite H7. lra. rewrite pow2_sqrt; lra.
  - set (δ := Rmin (a / 2) ((√(a/2) + √a) * ε)). exists δ. split.
    -- unfold δ. pose proof sqrt_lt_R0 a ltac:(lra) as H3.
       pose proof sqrt_lt_R0 (a / 2) ltac:(apply Rdiv_pos_pos; lra) as H4. solve_min.
    -- intros x H3. assert (|(x - a)| < a / 2) as H4 by (unfold δ in *; solve_R).
       assert (|(x - a)| < (√(a / 2) + √a) * ε) as H5 by (unfold δ in *; solve_R).
       assert (x < 0 \/ x >= 0) as [H6 | H6] by lra.
       * rewrite sqrt_neg_0; try lra. solve_abs.
       * pose proof sqrt_limit_helper_2 x a ltac:(lra) ltac:(lra) as H7.
         rewrite sqrt_limit_helper_1; try lra. apply Rmult_lt_reg_r with (r := √x + √a); try nra.
         field_simplify; nra.
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

Lemma right_limit_continuous_comp :
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

Lemma left_limit_continuous_comp :
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

Lemma limit_comp : ∀ (f g : ℝ → ℝ) (a b l : ℝ),
  ⟦ lim a ⟧ g = b ->
  ⟦ lim b ⟧ f = l ->
  (∃ δ : ℝ, δ > 0 ∧ ∀ x, 0 < |x -a| < δ -> g x ≠ b) ->
  ⟦ lim a ⟧ (λ x, f (g x)) = l.
Proof.
  intros f g a b l H1 H2 H3 ε H4.
  specialize (H2 ε H4) as [δ1 [H5 H6]].
  specialize (H1 δ1 H5) as [δ2 [H7 H8]].
  destruct H3 as [δ3 [H9 H10]].
  set (δ := Rmin δ2 δ3).
  assert (δ > 0) as H11 by (unfold δ; solve_min). 
  exists δ. split; try lra.
  intros x H12.
  specialize (H8 x ltac:(unfold δ in *; solve_R)).
  specialize (H6 (g x)).
  assert (0 < |(g x - b)| < δ1) as H13.
  { specialize (H10 x ltac:(unfold δ in *; solve_R)). unfold δ in H12. solve_R. }
  specialize (H6 H13). auto.
Qed.

Lemma limit_sqrt_f_x : forall f a L,
  ⟦ lim a ⟧ f = L -> L >= 0 -> ⟦ lim a ⟧ (fun x => √(f x)) = √L.
Proof.
  intros f a L H1 H2. apply limit_continuous_comp; auto. apply limit_sqrt_x.
Qed.

Lemma limit_to_0_equiv : forall f1 f2 L,
  (forall x, x <> 0 -> f1 x = f2 x) -> ⟦ lim 0 ⟧ f1 = L -> ⟦ lim 0 ⟧ f2 = L.
Proof.
  intros f1 f2 L H1 H2 ε H3. specialize (H2 ε H3) as [δ [H4 H5]]. exists δ. split; auto.
  intros x H6. specialize (H5 x H6). rewrite <- H1; solve_R.
Qed.

Lemma right_limit_to_0_equiv : forall f1 f2 L,
  (forall x, x <> 0 -> f1 x = f2 x) -> ⟦ lim 0⁺ ⟧ f1 = L -> ⟦ lim 0⁺ ⟧ f2 = L.
Proof.
  intros f1 f2 L H1 H2 ε H3. specialize (H2 ε H3) as [δ [H4 H5]]. exists δ. split; auto.
  intros x H6. specialize (H5 x H6). rewrite <- H1; solve_R.
Qed.

Lemma left_limit_to_0_equiv : forall f1 f2 L,
  (forall x, x <> 0 -> f1 x = f2 x) -> ⟦ lim 0⁻ ⟧ f1 = L -> ⟦ lim 0⁻ ⟧ f2 = L.
Proof.
  intros f1 f2 L H1 H2 ε H3. specialize (H2 ε H3) as [δ [H4 H5]]. exists δ. split; auto.
  intros x H6. specialize (H5 x H6). rewrite <- H1; solve_R.
Qed.

Lemma limit_to_0_equiv' : forall f1 f2 L δ,
  δ > 0 -> (forall x, (x <> 0 /\ |x| < δ) -> f1 x = f2 x) -> ⟦ lim 0 ⟧ f1 = L -> ⟦ lim 0 ⟧ f2 = L.
Proof.
  intros f1 f2 L δ H1 H2 H3 ε H4. specialize (H3 ε H4) as [δ1 [H5 H6]].
  exists (Rmin δ1 δ). split; [solve_R |].
  intros x H7. specialize (H6 x ltac:(split; solve_R)). rewrite <- H2; solve_R.
Qed.

Lemma limit_to_a_equiv : forall f1 f2 a L,
  (forall x, x <> a -> f1 x = f2 x) -> ⟦ lim a ⟧ f1 = L -> ⟦ lim a ⟧ f2 = L.
Proof.
  intros f1 f2 a L H1 H2 ε H3. specialize (H2 ε H3) as [δ [H4 H5]]. exists δ. split; auto.
  intros x H6. specialize (H5 x H6). rewrite <- H1; solve_R.
Qed.

Lemma limit_to_a_equiv' : forall f1 f2 a L δ,
  δ > 0 -> (forall x, (x <> a /\ |x - a| < δ) -> f1 x = f2 x) -> ⟦ lim a ⟧ f1 = L -> ⟦ lim a ⟧ f2 = L.
Proof.
  intros f1 f2 a L δ H1 H2 H3 ε H4. specialize (H3 ε H4) as [δ1 [H5 H6]].
  exists (Rmin δ1 δ). split; [solve_R |].
  intros x H7. specialize (H6 x ltac:(split; solve_R)). rewrite <- H2; solve_R.
Qed.

Lemma right_limit_to_a_equiv : forall f1 f2 a L,
  (forall x, x <> a -> f1 x = f2 x) -> ⟦ lim a⁺ ⟧ f1 = L -> ⟦ lim a⁺ ⟧ f2 = L.  
Proof.
  intros f1 f2 a L H1 H2 ε H3. specialize (H2 ε H3) as [δ [H4 H5]]. exists δ. split; auto.
  intros x H6. specialize (H5 x H6). rewrite <- H1; solve_R.
Qed.

Lemma left_limit_to_a_equiv : forall f1 f2 a L,
  (forall x, x <> a -> f1 x = f2 x) -> ⟦ lim a⁻ ⟧ f1 = L -> ⟦ lim a⁻ ⟧ f2 = L.
Proof.
  intros f1 f2 a L H1 H2 ε H3. specialize (H2 ε H3) as [δ [H4 H5]]. exists δ. split; auto.
  intros x H6. specialize (H5 x H6). rewrite <- H1; solve_R.
Qed.

Lemma right_limit_to_a_equiv' : forall f1 f2 a L δ,
  δ > 0 -> (forall x, x > a /\ |x - a| < δ -> f1 x = f2 x) -> ⟦ lim a⁺ ⟧ f1 = L -> ⟦ lim a⁺ ⟧ f2 = L.
Proof.
  intros f1 f2 a L δ H1 H2 H3 ε H4. specialize (H3 ε H4) as [δ1 [H5 H6]].
  exists (Rmin δ1 δ). split; [solve_R |].
  intros x H7. specialize (H6 x ltac:(split; solve_R)). rewrite <- H2; solve_R.
Qed.

Lemma left_limit_to_a_equiv' : forall f1 f2 a L δ,
  δ > 0 -> (forall x, x < a /\ |x - a| < δ -> f1 x = f2 x) -> ⟦ lim a⁻ ⟧ f1 = L -> ⟦ lim a⁻ ⟧ f2 = L.
Proof.
  intros f1 f2 a L δ H1 H2 H3 ε H4. specialize (H3 ε H4) as [δ1 [H5 H6]].
  exists (Rmin δ1 δ). split; [solve_R |].
  intros x H7. specialize (H6 x ltac:(split; solve_R)). rewrite <- H2; solve_R.
Qed.

Lemma squeeze_theorem : ∀ f1 f2 f3 a b c L,
  a < b -> c ∈ (a, b) -> ⟦ lim c ⟧ f1 = L -> ⟦ lim c ⟧ f3 = L -> (∀ x, x ∈ ((a, c) ⋃ (c, b)) -> f1 x <= f2 x <= f3 x) -> ⟦ lim c ⟧ f2 = L.
Proof.
  intros f1 f2 f3 a b c L H1 H2 H3 H4 H5 ε H6. specialize (H3 ε H6) as [δ1 [H7 H8]].
  specialize (H4 ε H6) as [δ2 [H9 H10]]. set (δ := Rmin δ1 (Rmin δ2 (Rmin (b - c) (c - a)))). unfold Ensembles.In in *.
  assert (δ > 0) as H11 by (unfold δ; solve_min). exists δ. split; auto. intros x H12. specialize (H8 x ltac:(unfold δ in *; solve_R)).
  specialize (H10 x ltac:(unfold δ in *; solve_R)).
  assert (x ∈ ((a, c) ⋃ (c, b))) as H13. {
    assert (x < c \/ x > c) as [H14 | H14] by solve_R.
    - left. unfold Ensembles.In in *. unfold δ in *; solve_R.
    - right. unfold Ensembles.In in *. unfold δ in *; solve_R.
  }
  specialize (H5 x H13). assert (f1 x <= f2 x <= f3 x) as H15 by auto. solve_R.
Qed.

Lemma squeeze_theorem_right : forall f1 f2 f3 c b L,
  c < b -> ⟦ lim c⁺ ⟧ f1 = L -> ⟦ lim c⁺ ⟧ f3 = L -> (forall x, x ∈ (c, b) -> f1 x <= f2 x <= f3 x) -> ⟦ lim c⁺ ⟧ f2 = L.
Proof.
  intros f1 f2 f3 b c L H1 H2 H3 H4 ε H5. specialize (H3 ε H5) as [δ1 [H6 H7]].
  specialize (H2 ε H5) as [δ2 [H8 H9]]. set (δ := Rmin δ1 (Rmin δ2 (c - b))). unfold Ensembles.In in *.
  assert (δ > 0) as H10 by (unfold δ; solve_R). exists δ. split; auto. intros x H11. specialize (H7 x ltac:(unfold δ in *; solve_R)).
  specialize (H9 x ltac:(unfold δ in *; solve_R)).
  specialize (H4 x ltac:(unfold δ in *; solve_R)). 
  solve_R.
Qed.

Lemma squeeze_theorem_left : forall f1 f2 f3 a c L,
  a < c -> ⟦ lim c⁻ ⟧ f1 = L -> ⟦ lim c⁻ ⟧ f3 = L -> (forall x, x ∈ (a, c) -> f1 x <= f2 x <= f3 x) -> ⟦ lim c⁻ ⟧ f2 = L.
Proof.
  intros f1 f2 f3 a c L H1 H2 H3 H4 ε H5. specialize (H3 ε H5) as [δ1 [H6 H7]].
  specialize (H2 ε H5) as [δ2 [H8 H9]]. set (δ := Rmin δ1 (Rmin δ2 (c - a))). unfold Ensembles.In in *.
  assert (δ > 0) as H10 by (unfold δ; solve_R). exists δ. split; auto. intros x H11. specialize (H7 x ltac:(unfold δ in *; solve_R)).
  specialize (H9 x ltac:(unfold δ in *; solve_R)).
  specialize (H4 x ltac:(unfold δ in *; solve_R)). 
  solve_R.
Qed.

Lemma right_lim_equality_substitution : forall f a L1 L2,
  L1 = L2 -> ⟦ lim a⁺ ⟧ f = L1 -> ⟦ lim a⁺ ⟧ f = L2.
Proof.
  intros f a L1 L2 H1 H2 ε H4. specialize (H2 ε H4) as [δ [H5 H6]].
  exists δ; split; auto. intros x. specialize (H6 x). solve_abs.
Qed.

Lemma left_lim_equality_substitution : forall f a L1 L2,
  L1 = L2 -> ⟦ lim a⁻ ⟧ f = L1 -> ⟦ lim a⁻ ⟧ f = L2.
Proof.
  intros f a L1 L2 H1 H2 ε H4. specialize (H2 ε H4) as [δ [H5 H6]].
  exists δ; split; auto. intros x. specialize (H6 x). solve_abs.
Qed.

Lemma lim_equality_substitution : forall f a L1 L2,
  L1 = L2 -> ⟦ lim a ⟧ f = L1 -> ⟦ lim a ⟧ f = L2.
Proof.
  intros f a L1 L2 H1 H2 ε H4. specialize (H2 ε H4) as [δ [H5 H6]].
  exists δ; split; auto. intros x. specialize (H6 x). solve_abs.
Qed.

Ltac solve_lim :=
  try solve_R;
  match goal with
  | [ |- ⟦ lim ?a ⟧ ?f = ?rhs ] =>
      let L2' := eval cbv beta in (f a) in
      let L2 := eval simpl in L2' in
      let H := fresh "H" in
      assert (⟦ lim a ⟧ f = L2) as H by
        (repeat (first [
           apply limit_div
         | apply limit_pow
         | apply limit_mult
         | apply limit_inv
         | apply limit_plus
         | apply limit_minus
         | apply limit_sqrt_x
         | apply limit_id
         | apply limit_const
         | solve_R
         ])); apply (lim_equality_substitution f a L2 rhs);
      solve_R; auto
  end.

Inductive expr :=
| EVar
| EConst (c : R)
| EAdd (e1 e2 : expr)
| ESub (e1 e2 : expr)
| EMul (e1 e2 : expr)
| EDiv (e1 e2 : expr)
| EApp (f : R -> R) (e : expr).


Fixpoint eval (e : expr) (x : R) : R :=
  match e with
  | EVar => x
  | EConst c => c
  | EAdd e1 e2 => eval e1 x + eval e2 x
  | ESub e1 e2 => eval e1 x - eval e2 x
  | EMul e1 e2 => eval e1 x * eval e2 x
  | EDiv e1 e2 => eval e1 x / eval e2 x
  | EApp f e1 => f (eval e1 x)
  end.

Fixpoint defined_at (e : expr) (a : R) : Prop :=
  match e with
  | EVar | EConst _ => True
  | EAdd e1 e2 | ESub e1 e2 | EMul e1 e2 =>
      defined_at e1 a /\ defined_at e2 a
  | EDiv e1 e2 =>
      defined_at e1 a /\ defined_at e2 a /\ eval e2 a <> 0
  | EApp f e1 =>
      defined_at e1 a /\ ⟦ lim (eval e1 a) ⟧ f = f (eval e1 a)
  end.

Fixpoint defined_at_right (e : expr) (a : R) : Prop :=
  match e with
  | EVar | EConst _ => True
  | EAdd e1 e2 | ESub e1 e2 | EMul e1 e2 =>
      defined_at_right e1 a /\ defined_at_right e2 a
  | EDiv e1 e2 =>
      defined_at_right e1 a /\ defined_at_right e2 a /\ eval e2 a <> 0
  | EApp f e1 =>
      defined_at_right e1 a /\ ⟦ lim (eval e1 a)⁺ ⟧ f = f (eval e1 a)
  end.

Lemma right_limit_eval_expr :
  forall e a,
    defined_at e a ->
    ⟦ lim a⁺ ⟧ (fun x => eval e x) = eval e a.
Proof.
  induction e; intros a H; simpl in *; try solve_R.
  - apply right_limit_id.
  - apply right_limit_const.
  - destruct H as [H1 H2]. apply right_limit_plus; [now apply IHe1|now apply IHe2].
  - destruct H as [H1 H2]. apply right_limit_minus; [now apply IHe1|now apply IHe2].
  - destruct H as [H1 H2]. apply right_limit_mult; [now apply IHe1|now apply IHe2].
  - destruct H as [H1 [H2 Hnz]].
    apply right_limit_div; [now apply IHe1|now apply IHe2|exact Hnz].
  - destruct H as [Harg Hcont].
    eapply right_limit_continuous_comp; auto.
Qed.

Lemma left_limit_eval_expr :
  forall e a,
    defined_at e a ->
    ⟦ lim a⁻ ⟧ (fun x => eval e x) = eval e a.
Proof.
  induction e; intros a H; simpl in *; try solve_R.
  - apply left_limit_id.
  - apply left_limit_const.
  - destruct H as [H1 H2]. apply left_limit_plus; [now apply IHe1|now apply IHe2].
  - destruct H as [H1 H2]. apply left_limit_minus; [now apply IHe1|now apply IHe2].
  - destruct H as [H1 H2]. apply left_limit_mult; [now apply IHe1|now apply IHe2].
  - destruct H as [H1 [H2 Hnz]].
    apply left_limit_div; [now apply IHe1|now apply IHe2|exact Hnz].
  - destruct H as [Harg Hcont].
    eapply left_limit_continuous_comp; [ now apply IHe | exact Hcont ].
Qed.

Lemma limit_eval_expr :
  forall e a,
    defined_at e a ->
    ⟦ lim a ⟧ (fun x => eval e x) = eval e a.
Proof.
  intros e a H1. apply left_right_iff; split.
  - apply left_limit_eval_expr; auto.
  - apply right_limit_eval_expr; auto.
Qed.

Ltac reify_expr x t :=
  lazymatch t with
  | x                 => constr:(EVar)
  | ?u / ?v           => let e1 := reify_expr x u in
                         let e2 := reify_expr x v in
                         constr:(EDiv e1 e2)
  | ?u * ?v           => let e1 := reify_expr x u in
                         let e2 := reify_expr x v in
                         constr:(EMul e1 e2)
  | ?u + ?v           => let e1 := reify_expr x u in
                         let e2 := reify_expr x v in
                         constr:(EAdd e1 e2)
  | ?u - ?v           => let e1 := reify_expr x u in
                         let e2 := reify_expr x v in
                         constr:(ESub e1 e2)
  | - ?u              => let e := reify_expr x u in
                         constr:(ESub (EConst 0%R) e)

  | ?h ?u             =>
      let Th := type of h in
      lazymatch Th with
      | R -> R =>
          lazymatch u with
          | context[x] =>
              let e1 := reify_expr x u in
              constr:(EApp h e1)
          | _ =>
              lazymatch type of (h u) with
              | R => constr:(EConst (h u))
              | _ => fail "reify_expr: (h u) is not R-valued"
              end
          end
      | _ =>
          lazymatch type of t with
          | R        => constr:(EConst t)
          | Z        => let r := constr:(IZR t) in constr:(EConst r)
          | nat      => let z := constr:(Z.of_nat t) in
                        let r := constr:(IZR z) in constr:(EConst r)
          | positive => let z := constr:(Zpos t) in
                        let r := constr:(IZR z) in constr:(EConst r)
          | _        => fail "reify_expr: unsupported non-R application:" t
          end
      end

  | ?c =>
      lazymatch type of c with
      | R        => constr:(EConst c)
      | Z        => let r := constr:(IZR c) in constr:(EConst r)
      | nat      => let z := constr:(Z.of_nat c) in
                    let r := constr:(IZR z) in constr:(EConst r)
      | positive => let z := constr:(Zpos c) in
                    let r := constr:(IZR z) in constr:(EConst r)
      | _        => fail "reify_expr: unsupported constant:" c
      end
  end.

Ltac change_fun_to_expr :=
  let reify_current f :=
    let x := fresh "x" in
    intros x _;
    let fx := (eval cbv beta in (f x)) in
    let ex := reify_expr x fx in
    instantiate (1 := fun y => eval ex y);
    reflexivity
  in
  lazymatch goal with
  | |- forall _, _ => intro; change_fun_to_expr
  | |- ?P -> _     => intro; change_fun_to_expr
  | |- ⟦ lim ?a ⟧ ?f = ?L =>
      eapply limit_to_a_equiv; [ reify_current f | ]
  | |- ⟦ lim ?a ⁺ ⟧ ?f = ?L =>
      eapply right_limit_to_a_equiv; [ reify_current f | ]
  | |- ⟦ lim ?a ⁻ ⟧ ?f = ?L =>
      eapply left_limit_to_a_equiv; [ reify_current f | ]
  | _ => fail "No matching goal found"
  end.


Ltac solve_defined_at :=
  repeat match goal with
  | |- defined_at EVar _ => exact I
  | |- defined_at (EConst _) _ => exact I
  | |- defined_at (EAdd _ _) _ => split
  | |- defined_at (ESub _ _) _ => split
  | |- defined_at (EMul _ _) _ => split
  | |- defined_at (EDiv _ _) _ => repeat split
  | |- defined_at (EApp ?f ?e) ?a =>
      split; [ solve_defined_at | auto ]
  end; solve_R.



Ltac finish_with_eval :=
  lazymatch goal with
  | |- ⟦ lim ?a ⟧ (fun _ => eval ?e _) = ?L =>
      eapply (lim_equality_substitution (fun _ => eval e _) a (eval e a) L);
      [ solve_R | apply limit_eval_expr; auto ]
  | |- ⟦ lim ?a ⁺ ⟧ (fun _ => eval ?e _) = ?L =>
      eapply (right_lim_equality_substitution (fun _ => eval e _) a (eval e a) L);
      [ solve_R | apply right_limit_eval_expr; auto ]
  | |- ⟦ lim ?a ⁻ ⟧ (fun _ => eval ?e _) = ?L =>
      eapply (left_lim_equality_substitution (fun _ => eval e _) a (eval e a) L);
      [ solve_R | apply left_limit_eval_expr; auto ]
  | _ => fail "No matching goal found"
  end.

  
Ltac auto_limit :=
  intros; solve_R;
  change_fun_to_expr;
  match goal with
  | |- ⟦ lim ?a ⟧ (fun x => eval ?ex x) = ?L =>
      assert (defined_at ex a) by (solve_defined_at; solve_R)
  | |- ⟦ lim ?a ⁺ ⟧ (fun x => eval ?ex x) = ?L =>
      assert (defined_at ex a) by (solve_defined_at; solve_R)
  | |- ⟦ lim ?a ⁻ ⟧ (fun x => eval ?ex x) = ?L =>
      assert (defined_at ex a) by (solve_defined_at; solve_R)
  end;
  finish_with_eval.


Lemma lim_div_test : forall f,
  ⟦ lim 2⁺ ⟧ (fun x => (x * x - 1) / (x - 1) * (x - 19) + f 1) = (-51 + (f 1)).
Proof.
  intros. change_fun_to_expr.
  auto_limit.
Qed.