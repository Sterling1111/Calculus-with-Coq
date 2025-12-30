From Lib Require Import Imports Sets Notations Functions Limit Continuity Reals_util Sums Interval.
Import SetNotations IntervalNotations Function_Notations LimitNotations.

Definition differentiable_at (f:R -> R) (a:R) :=
  exists L, ⟦ lim 0 ⟧ (fun h => (f (a + h) - f a) / h) = L.

Definition differentiable_at_left (f:R -> R) (a:R) :=
  exists L, ⟦ lim 0⁻ ⟧ (fun h => (f (a + h) - f a) / h) = L.

Definition differentiable_at_right (f:R -> R) (a:R) :=
  exists L, ⟦ lim 0⁺ ⟧ (fun h => (f (a + h) - f a) / h) = L.

Definition differentiable_domain (D : Ensemble R) :=
  forall x, x ∈ D -> (interior_point D x \/ left_endpoint D x \/ right_endpoint D x).

Definition differentiable_on (f:R -> R) (A:Ensemble R) :=
  forall a, a ∈ A ->
    ((interior_point A a /\ differentiable_at f a) \/
     (left_endpoint A a /\ differentiable_at_right f a) \/
     (right_endpoint A a /\ differentiable_at_left f a)).

Definition differentiable (f:R -> R) :=
  forall x, differentiable_at f x.

Definition derivative_at (f f' : R -> R) (a : R) :=
  ⟦ lim 0 ⟧ (fun h => (f (a + h) - f a) / h) = f' a.

Definition derivative_at_left (f f' : R -> R) (a : R) :=
  ⟦ lim 0⁻ ⟧ (fun h => (f (a + h) - f a) / h) = f' a.

Definition derivative_at_right (f f' : R -> R) (a : R) :=
  ⟦ lim 0⁺ ⟧ (fun h => (f (a + h) - f a) / h) = f' a.

Definition derivative_on (f f' : R -> R) (A : Ensemble R) :=
  forall a, a ∈ A ->
    ((interior_point A a /\ derivative_at f f' a) \/
     (left_endpoint A a /\ derivative_at_right f f' a) \/
     (right_endpoint A a /\ derivative_at_left f f' a)).

Definition derivative (f f' : R -> R) :=
  forall x, derivative_at f f' x.

Fixpoint nth_derivative (n:nat) (f fn' : R -> R) : Prop :=
  match n with
  | 0   => f = fn'
  | S k => exists f', derivative f f' /\ nth_derivative k f' fn'
  end.

Definition nth_differentiable (n : nat) (f : R -> R) : Prop :=
  exists fn', nth_derivative n f fn'.

Fixpoint nth_derivative_on (n : nat) (f fn' : R -> R) (D : Ensemble R) : Prop :=
  match n with
  | 0   => forall x, x ∈ D -> f x = fn' x
  | S k => exists f', derivative_on f f' D /\ nth_derivative_on k f' fn' D
  end.

Definition nth_derivative_at (n : nat) (f fn' : R -> R) (a : R) : Prop :=
  match n with
  | 0   => f a = fn' a
  | S k => exists δ (fk : R -> R),
             δ > 0 /\
             nth_derivative_on k f fk (fun x => a - δ < x < a + δ) /\
             derivative_at fk fn' a
  end.

Definition nth_differentiable_at (n : nat) (f : R -> R) (a : R) : Prop :=
  exists fn', nth_derivative_at n f fn' a.

Definition nth_differentiable_on (n : nat) (f : R -> R) (D : Ensemble R) : Prop :=
  exists fn', nth_derivative_on n f fn' D.

Definition is_derivative_val_at (f : R -> R) (x : R) (L : R) : Prop :=
  ⟦ lim 0 ⟧ (fun h => (f (x + h) - f x) / h) = L.

Definition is_derive_val_or_zero (f : R -> R) (x L : R) : Prop :=
  (is_derivative_val_at f x L) \/ (~differentiable_at f x /\ L = 0).

Definition Derive_at (f : R -> R) (x : R) : R :=
  epsilon (inhabits 0) (is_derive_val_or_zero f x).

Definition Derive (f : R -> R) : R -> R :=
  fun x => Derive_at f x.

Fixpoint nth_Derive (n:nat) (f : R -> R) : R -> R :=
  match n with
  | 0   => f
  | S k => Derive (nth_Derive k f)
  end.

Definition nth_Derive_at (n:nat) (f : R -> R) (a : R) : R :=
  nth_Derive n f a.

Definition is_derive_on_or_zero (f : R -> R) (D : Ensemble R) (g : R -> R) : Prop :=
  (derivative_on f g D) \/ (~(exists h, derivative_on f h D) /\ g = (fun _ => 0)).

Definition Derive_on (f : R -> R) (D : Ensemble R) : R -> R :=
  epsilon (inhabits (fun _ => 0)) (is_derive_on_or_zero f D).

Fixpoint nth_Derive_on (n : nat) (f : R -> R) (D : Ensemble R) : R -> R :=
  match n with
  | 0   => f
  | S k => Derive_on (nth_Derive_on k f D) D
  end.

Definition inf_differentiable (f : R -> R) : Prop :=
  forall n, exists fn', nth_derivative n f fn'.

Module DerivativeNotations.
  Declare Scope derivative_scope.
  Delimit Scope derivative_scope with d.

  Notation "⟦ 'der' ⟧ f = f'" := (derivative f f')
    (at level 70, f at level 0, no associativity, format "⟦  'der'  ⟧  f  =  f'") : derivative_scope.

  Notation "'der' f = f'" := (derivative f f')
    (at level 70, f at level 0, no associativity, only parsing) : derivative_scope.

  Notation "⟦ 'der' ⟧ f D = f'" := (derivative_on f f' D)
    (at level 70, f at level 0, D at level 0, no associativity, format "⟦  'der'  ⟧  f  D  =  f'") : derivative_scope.

  Notation "⟦ 'der' a ⟧ f = f'" := (derivative_at f f' a)
    (at level 70, f at level 0, no associativity, format "⟦  'der'  a  ⟧  f  =  f'") : derivative_scope.

  Notation "⟦ 'der' a ⁺ ⟧ f = f'" := (derivative_at_right f f' a)
    (at level 70, f at level 0, no associativity, format "⟦  'der'  a ⁺  ⟧  f  =  f'") : derivative_scope.

  Notation "⟦ 'der' a ⁻ ⟧ f = f'" := (derivative_at_left f f' a)
    (at level 70, f at level 0, no associativity, format "⟦  'der'  a ⁻  ⟧  f  =  f'") : derivative_scope.

  Notation "⟦ 'der' ^ n ⟧ f = fn" := (nth_derivative n f fn)
    (at level 70, n at level 0, f at level 0, no associativity,
      format "⟦  'der' ^ n  ⟧  f  =  fn") : derivative_scope.

  Notation "⟦ 'der' ^ n ⟧ f D = fn" := (nth_derivative_on n f fn D)
    (at level 70, n at level 0, f at level 0, D at level 0, no associativity,
      format "⟦  'der' ^ n  ⟧  f  D  =  fn") : derivative_scope.

  Notation "⟦ 'der' ^ n a ⟧ f = fn'" := (nth_derivative_at n f fn' a)
    (at level 70, n at level 0, f at level 0, no associativity,
    format "⟦  'der' ^ n  a  ⟧  f  =  fn'") : derivative_scope.

  Notation "⟦ 'Der' ⟧ f" := (Derive f)
    (at level 70, f at level 0, no associativity, format "⟦  'Der'  ⟧  f") : derivative_scope.

  Notation "⟦ 'Der' a ⟧ f" := (Derive_at f a)
    (at level 70, a at level 9, f at level 0, no associativity, format "⟦  'Der'  a  ⟧  f") : derivative_scope.

  Notation "⟦ 'Der' ⟧ f D" := (Derive_on f D)
    (at level 70, f at level 0, D at level 0, no associativity, format "⟦  'Der'  ⟧  f  D") : derivative_scope.

  Notation "⟦ 'Der' ^ n ⟧ f" := (nth_Derive n f)
    (at level 70, n at level 9, f at level 0, no associativity, format "⟦  'Der' ^ n  ⟧  f") : derivative_scope.

  Notation "⟦ 'Der' ^ n ⟧ f D" := (nth_Derive_on n f D)
    (at level 70, n at level 9, f at level 0, D at level 0, no associativity, format "⟦  'Der' ^ n  ⟧  f  D") : derivative_scope.

  Notation "⟦ 'Der' ^ n a ⟧ f" := (nth_Derive_at n f a)
    (at level 70,
      n at level 9,
      a at level 9,
      f at level 0,
      no associativity, format "⟦  'Der' ^ n  a  ⟧  f") : derivative_scope.

End DerivativeNotations.

Import DerivativeNotations.

Open Scope derivative_scope.

Theorem derivative_at_unique : forall f f1' f2' x,
  ⟦ der x ⟧ f = f1' -> ⟦ der x ⟧ f = f2' -> f1' x = f2' x.
Proof.
  intros f f1' f2' x H1 H2. unfold derivative_at in *. 
  apply (limit_unique (fun h => (f (x + h) - f x) / h) 0 (f1' x) (f2' x)); auto.
Qed.

Theorem derivative_at_left_unique : forall f f1' f2' x,
  ⟦ der x⁻ ⟧ f = f1' -> ⟦ der x⁻ ⟧ f = f2' -> f1' x = f2' x.
Proof.
  intros f f1' f2' x H1 H2. unfold derivative_at_left in *. 
  apply (limit_left_unique (fun h => (f (x + h) - f x) / h) 0 (f1' x) (f2' x)); auto.
Qed.

Theorem derivative_at_right_unique : forall f f1' f2' x,
  ⟦ der x⁺ ⟧ f = f1' -> ⟦ der x⁺ ⟧ f = f2' -> f1' x = f2' x.
Proof.
  intros f f1' f2' x H1 H2. unfold derivative_at_right in *. 
  apply (limit_right_unique (fun h => (f (x + h) - f x) / h) 0 (f1' x) (f2' x)); auto.
Qed.

Theorem derivative_unique : forall f f1' f2',
  ⟦ der ⟧ f = f1' -> ⟦ der ⟧ f = f2' -> f1' = f2'.
Proof.
  intros f f1' f2' H1 H2. extensionality x. 
  apply (derivative_at_unique f f1' f2' x); auto.
Qed.

Lemma derivative_on_unique : forall f f1' f2' D,
  ⟦ der ⟧ f D = f1' -> ⟦ der ⟧ f D = f2' -> forall x, x ∈ D -> f1' x = f2' x.
Proof.
  intros f f1' f2' D H1 H2 x H3.
  specialize (H1 x H3).
  specialize (H2 x H3).
  destruct H1 as [[H4 H5] | [[H4 H5] | [H4 H5]]]; destruct H2 as [[H6 H7] | [[H6 H7] | [H6 H7]]].
  - eapply derivative_at_unique; eauto.
  - exfalso. apply (interior_not_endpoint D x H4). left; auto.
  - exfalso. apply (interior_not_endpoint D x H4). right; auto.
  - exfalso. apply (interior_not_endpoint D x H6). left; auto.
  - eapply derivative_at_right_unique; eauto.
  - exfalso. destruct H4 as [δ1 [H8 H9]]. destruct H6 as [δ2 [H10 H11]].
    set (y := x + Rmin δ1 δ2 / 2).
    specialize (H9 y). assert (H12: y ∈ [x, x + δ1)) by (unfold y in *; solve_R).
    destruct H9 as [_ H9]. specialize (H9 H12).
    specialize (H11 y). assert (H13: y ∈ (x, x + δ2]) by (unfold y in *; solve_R).
    destruct H11 as [H11 _]. specialize (H11 H13).
    contradiction.
  - exfalso. apply (interior_not_endpoint D x H6). right; auto.
  - destruct H4 as [δ1 [H8 H9]]. destruct H6 as [δ2 [H10 H11]].
    set (y := x - Rmin δ1 δ2 / 2).
    specialize (H9 y). assert (H12: y ∈ (x - δ1, x]) by (unfold y in *; solve_R).
    destruct H9 as [_ H9]. specialize (H9 H12).
    specialize (H11 y). assert (H13: y ∈ [x - δ2, x)) by (unfold y in *; solve_R).
    destruct H11 as [H11 _]. specialize (H11 H13).
    contradiction.
  - eapply derivative_at_left_unique; eauto.
Qed.

Lemma nth_derivative_unique : forall n f fn1' fn2',
  ⟦ der ^ n ⟧ f = fn1' -> ⟦ der ^ n ⟧ f = fn2' -> fn1' = fn2'.
Proof.
  induction n as [| k IH]; intros f fn1' fn2' H1 H2.
  - simpl in H1, H2. subst. reflexivity.
  - destruct H1 as [f1' [H1 H3]], H2 as [f2' [H2 H4]].
    pose proof (derivative_unique f f1' f2' H1 H2) as H5.
    subst f2'.
    apply (IH f1' fn1' fn2'); auto.
Qed.

Theorem derivative_on_ext : forall f f1' f2' D,
  (forall x, x ∈ D -> f1' x = f2' x) -> 
  ⟦ der ⟧ f D = f1' -> 
  ⟦ der ⟧ f D = f2'.
Proof.
  intros f f1' f2' D H1 H2 x H3.
  specialize (H2 x H3).
  destruct H2 as [[H4 H5] | [[H4 H5] | [H4 H5]]];
  [ left | right; left | right; right ]; split; auto.
  - unfold derivative_at in *. rewrite <- H1; auto.
  - unfold derivative_at_right in *. rewrite <- H1; auto.
  - unfold derivative_at_left in *. rewrite <- H1; auto.
Qed.

Lemma limit_diff_zero_iff_continuous : forall f a,
  ⟦ lim 0 ⟧ (fun h => (f (a + h) - f a)) = 0 <-> ⟦ lim a ⟧ f = f a.
Proof.
  intros f a. split; intros H1 ε H2.
  - specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto. intros x H5.
    specialize (H4 (x - a) ltac:(solve_R)). replace (a + (x - a)) with x in H4; solve_R.
  - specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto. intros x H5.
    specialize (H4 (a + x) ltac:(solve_R)). replace (a + x - a) with x in H4; solve_R.
Qed.

Lemma limit_right_diff_zero_iff_continuous : forall f a,
  ⟦ lim 0⁺ ⟧ (fun h => (f (a + h) - f a)) = 0 <-> ⟦ lim a⁺ ⟧ f = f a.
Proof.
  intros f a. split; intros H1 ε H2.
  - specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto. intros x H5.
    specialize (H4 (x - a) ltac:(solve_R)). replace (a + (x - a)) with x in H4; solve_R.
  - specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto. intros x H5.
    specialize (H4 (a + x) ltac:(solve_R)). replace (a + x - a) with x in H4; solve_R.
Qed.

Lemma limit_left_diff_zero_iff_continuous : forall f a,
  ⟦ lim 0⁻ ⟧ (fun h => (f (a + h) - f a)) = 0 <-> ⟦ lim a⁻ ⟧ f = f a.
Proof.
  intros f a. split; intros H1 ε H2.
  - specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto. intros x H5.
    specialize (H4 (x - a) ltac:(solve_R)). replace (a + (x - a)) with x in H4; solve_R.
  - specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto. intros x H5.
    specialize (H4 (a + x) ltac:(solve_R)). replace (a + x - a) with x in H4; solve_R.
Qed.

Lemma derivative_at_iff : forall f f' a,
  ⟦ der a ⟧ f = f' <-> ⟦ der a⁺ ⟧ f = f' /\ ⟦ der a⁻ ⟧ f = f'.
Proof.
  intros f f' a.
  split; intros H1.
  - unfold derivative_at in *. split.
    -- unfold derivative_at_right, derivative_at_left in *.
       apply limit_iff in H1. tauto.
    -- unfold derivative_at_right, derivative_at_left in *.
       apply limit_iff in H1. tauto.
  - unfold derivative_at. apply limit_iff. split; tauto.
Qed.

Lemma differentiable_at_imp_left_right : forall f a,
  differentiable_at f a -> differentiable_at_right f a /\ differentiable_at_left f a.
Proof.
  intros f a [L H1]. split.
  - exists L. intros ε H2. specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto.
    intros x H5. specialize (H4 x ltac:(solve_R)). auto.
  - exists L. intros ε H2. specialize (H1 ε H2) as [δ [H3 H4]]. exists δ. split; auto.
    intros x H5. specialize (H4 x ltac:(solve_R)). auto.
Qed.

Lemma differentiable_at_imp_exists_derivative : forall f a,
  differentiable_at f a -> exists f', ⟦ der a ⟧ f = f'.
Proof.
  intros f a [L H1]. 
  exists (fun _ => L). 
  apply H1.
Qed.

Lemma derivative_imp_derivative_on : forall f f' D,
  differentiable_domain D ->
   ⟦ der ⟧ f = f' -> ⟦ der ⟧ f D = f'.
Proof.
  intros f f' D H1 H2 a H3. destruct (H1 a H3) as [H4 | [H4 | H4]].
  - left. split; auto.
  - right; left. split; auto. specialize (H2 a). apply derivative_at_iff in H2; tauto.
  - right; right. split; auto. specialize (H2 a). apply derivative_at_iff in H2; tauto.
Qed.

Lemma derivative_imp_derivative_on_closed : forall f f' a b,
  a < b ->
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ f [a, b] = f'.
Proof.
  intros f f' a b H1 H2. apply derivative_imp_derivative_on; auto.
  intros x H3. pose proof unique_classification_closed x a b H1 H3. tauto.
Qed.

Lemma derivative_imp_derivative_on_open : forall f f' a b,
  a < b ->
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ f (a, b) = f'.
Proof.
  intros f f' a b H1 H2. apply derivative_imp_derivative_on; auto.
  intros x H3. left. apply open_interior_iff; auto.
Qed.

Theorem differentiable_at_imp_continuous_at : forall f a,
  differentiable_at f a -> continuous_at f a.
Proof.
  intros f a [L H1]. apply limit_diff_zero_iff_continuous.
  assert (⟦ lim 0 ⟧ (fun h => (f (a + h) - f a) / h * h) = 0) as H2.
  { replace 0 with (L * 0) at 2 by lra. apply limit_mult. 2 : { apply limit_id. } auto. }
  apply limit_eq with (f1 := fun h => (f (a + h) - f a) / h * h); auto.
  exists 1. split; [ lra | ]. intros x H3. solve_R.
Qed.

Theorem differentiable_at_right_imp_continuous_at_right : forall f a,
  differentiable_at_right f a -> continuous_at_right f a.
Proof.
  intros f a [L H1]. apply limit_right_diff_zero_iff_continuous.
  assert (⟦ lim 0⁺ ⟧ (fun h => (f (a + h) - f a) / h * h) = 0) as H2.
  { replace 0 with (L * 0) at 2 by lra. apply limit_right_mult. 2 : { apply limit_right_id. } auto. }
  apply limit_right_eq with (f1 := fun h => (f (a + h) - f a) / h * h); auto.
  exists 1. split; [ lra | ]. intros x H3. solve_R.
Qed.

Theorem differentiable_at_left_imp_continuous_at_left : forall f a,
  differentiable_at_left f a -> continuous_at_left f a.
Proof.
  intros f a [L H1]. apply limit_left_diff_zero_iff_continuous.
  assert (⟦ lim 0⁻ ⟧ (fun h => (f (a + h) - f a) / h * h) = 0) as H2.
  { replace 0 with (L * 0) at 2 by lra. apply limit_left_mult. 2 : { apply limit_left_id. } auto. }
  apply limit_left_eq with (f1 := fun h => (f (a + h) - f a) / h * h); auto.
  exists 1. split; [ lra | ]. intros x H3. solve_R.
Qed.

Lemma differentiable_imp_continuous : forall f,
  differentiable f -> continuous f.
Proof.
  intros f H1 x. apply differentiable_at_imp_continuous_at. apply H1.
Qed.

Theorem differentiable_on_imp_continuous_on_closed : forall f a b,
  a < b -> differentiable_on f [a, b] -> continuous_on f [a, b].
Proof.
  intros f a b H1 H2. apply continuous_on_closed_interval_iff; auto. repeat split.
  - intros x H3. specialize (H2 x ltac:(solve_R)) as [H2 | [H2 | H2]].
    -- apply differentiable_at_imp_continuous_at; tauto.
    -- exfalso. apply (closed_not_left_pt_interior a b x H1 H3); tauto.
    -- exfalso. apply (closed_not_right_pt_interior a b x H1 H3); tauto.
  - specialize (H2 a ltac:(solve_R)) as [H2 | [H2 | H2]].
    -- exfalso. apply (closed_not_interior_a a b H1); tauto.
    -- apply differentiable_at_right_imp_continuous_at_right; tauto.
    -- exfalso. apply (closed_not_right_pt_a a b H1); tauto.
  - specialize (H2 b ltac:(solve_R)) as [H2 | [H2 | H2]].
    -- exfalso. apply (closed_not_interior_b a b H1); tauto.
    -- exfalso. apply (closed_not_left_pt_b a b H1); tauto.
    -- apply differentiable_at_left_imp_continuous_at_left; tauto.
Qed.

Theorem differentiable_on_imp_continuous_on_open : forall f a b,
  a < b -> differentiable_on f (a, b) -> continuous_on f (a, b).
Proof.
  intros f a b H1 H2 x H3. specialize (H2 x H3) as [[H2 H4] | [[H2 _] | [H2 _]]].
    -- apply differentiable_at_imp_continuous_at in H4. unfold continuous_at in H4. intros ε H5.
       specialize (H4 ε H5) as [δ [H6 H7]]. exists δ; split; auto.
    -- exfalso. apply (open_not_left_pt a b x H1); auto.
    -- exfalso. apply (open_not_right_pt a b x H1); auto.
Qed.

Lemma differentiable_on_closed_interval_subset : forall f a b c d,
  a <= c < d <= b -> differentiable_on f [a, b] -> differentiable_on f [c, d].
Proof.
  intros f a b c d H1 H2 x H4. specialize (H2 x ltac:(solve_R)) as [[H5 H6] | [[H5 H6] | [H5 H6]]].
  - apply unique_classification_closed in H4 as [H7 | [H7 | H7]]; solve_R.
    -- right. left. split; auto. apply differentiable_at_imp_left_right; auto.
    -- right; right; split; auto. apply differentiable_at_imp_left_right; auto.
  - right. left. split; auto. apply closed_left_pt_iff; apply closed_left_pt_iff in H5; solve_R.
  - right; right; split; auto. apply closed_right_pt_iff; apply closed_right_pt_iff in H5; solve_R.
Qed.

Lemma differentiable_on_open_interval_subset : forall f a b c d,
  a <= c < d <= b -> differentiable_on f [a, b] -> differentiable_on f (c, d).
Proof.
  intros f a b c d H1 H2 x H4. specialize (H2 x ltac:(solve_R)) as [[H5 H6] | [[H5 H6] | [H5 H6]]].
  - left. split; auto. apply open_interior_iff; solve_R.
  - apply closed_left_pt_iff in H5; solve_R.
  - apply closed_right_pt_iff in H5; solve_R.
Qed.

Lemma continuous_on_closed_interval_subset : forall f a b c d,
a <= c < d <= b -> continuous_on f [a, b] -> continuous_on f [c, d].
Proof.
  intros f a b c d H1 H2. apply continuous_on_closed_interval_iff in H2 as [H3 [H5 H6]]; solve_R.
  apply continuous_on_closed_interval_iff; solve_R. repeat split.
  - intros x H7. apply H3. solve_R.
  - assert (a < c \/ a = c) as [H7 | H7] by solve_R.
    -- specialize (H3 c ltac:(solve_R)). apply limit_iff in H3. tauto.
    -- subst. auto.
  - assert (b > d \/ b = d) as [H7 | H7] by solve_R.
    -- specialize (H3 d ltac:(solve_R)). apply limit_iff in H3. tauto.
    -- subst. tauto.
Qed.

Lemma differentiable_imp_differentiable_on : forall f a b,
  a < b -> differentiable f -> differentiable_on f [a, b].
Proof.
  intros f  a b H1 H2 x H3. assert (x = a \/ x = b \/ (a < x < b)) as [H4 | [H4 | H4]] by solve_R.
  - right; left. split. subst. apply closed_left_pt_iff; auto.
    apply differentiable_at_imp_left_right. auto.
  - right; right. split. subst. apply closed_right_pt_iff; auto.
    apply differentiable_at_imp_left_right. auto.
  - left. split. apply closed_interior_iff; solve_R.
    apply H2.
Qed.

Lemma derivative_imp_differentiable : forall f f',
  ⟦ der ⟧ f = f' -> differentiable f.
Proof.
  intros f f' H1 x. unfold differentiable_at. exists (f' x). intros ε H2.
  specialize (H1 x ε) as [δ [H3 H4]]; auto. exists δ. split; auto.
Qed.

Lemma differentiable_imp_exists_derivative : forall f,
  differentiable f -> exists f', ⟦ der ⟧ f = f'.
Proof.
  intros f H1.
  unfold derivative.
  apply choice with (A := R) (B := R) (R := fun x y => ⟦ lim 0 ⟧ (fun h => (f (x + h) - f x) / h) = y).
  intros x.
  specialize (H1 x).
  unfold differentiable_at in H1.
  destruct H1 as [L H1].
  exists L.
  unfold derivative_at.
  apply H1.
Qed.

Lemma differentiable_on_imp_differentiable_at : forall f D a,
  a ∈ D -> 
  interior_point D a -> 
  differentiable_on f D -> 
  differentiable_at f a.
Proof.
  intros f D a H1 H2 H3.
  specialize (H3 a H1) as [[H4 H5] | [[H4 H5] | [H4 H5]]]; auto.
  - exfalso. apply interior_not_endpoint in H2. tauto.
  - exfalso. apply interior_not_endpoint in H2. tauto.
Qed.

Lemma derivative_at_imp_differentiable_at : forall a f f',
  ⟦ der a ⟧ f = f' -> differentiable_at f a.
Proof.
  intros a f f' H1. exists (f' a). auto.
Qed.

Lemma derivative_at_right_imp_differentiable_at_right : forall a f f',
  ⟦ der a⁺ ⟧ f = f' -> differentiable_at_right f a.
Proof.
  intros a f f' H1. exists (f' a). auto.
Qed.

Lemma derivative_at_left_imp_differentiable_at_left : forall a f f',
  ⟦ der a⁻ ⟧ f = f' -> differentiable_at_left f a.
Proof.
  intros a f f' H1. exists (f' a). auto.
Qed.

Lemma derivative_on_imp_differentiable_on : forall f f' A,
  ⟦ der ⟧ f A = f' -> differentiable_on f A.
Proof.
  intros f f' A H1 x H2. specialize (H1 x H2) as [H3 | [H3 | H3]].
  - left. split; try tauto. apply (derivative_at_imp_differentiable_at x f f'); tauto.
  - right. left. split; try tauto. apply (derivative_at_right_imp_differentiable_at_right x f f'); tauto.
  - right. right. split; try tauto. apply (derivative_at_left_imp_differentiable_at_left x f f'); tauto.
Qed.

Lemma differentiable_domain_open : forall a b,
  a < b -> differentiable_domain (a, b).
Proof.
  intros a b H1 x H2.
  left. apply open_interior_iff; solve_R.
Qed.

Lemma differentiable_domain_closed : forall a b,
  a < b -> differentiable_domain [a, b].
Proof.
  intros a b H1 x H2.
  pose proof unique_classification_closed x a b H1 H2. tauto.
Qed.

Lemma derivative_at_const : forall c a,
  ⟦ der a ⟧ (fun _ => c) = (fun _ => 0).
Proof.
  intros c a. apply limit_eq with (f1 := fun h => 0).
  - exists 1. split; [ lra | ]. intros x H1. solve_R.
  - apply limit_const.
Qed.

Lemma derivative_at_right_const : forall c a,
  ⟦ der a ⁺ ⟧ (fun _ => c) = (fun _ => 0).
Proof.
  intros c a. apply limit_right_eq with (f1 := fun h => 0).
  - exists 1. split; [ lra | ]. intros x H1. solve_R.
  - apply limit_right_const.
Qed.

Lemma derivative_at_left_const : forall c a,
  ⟦ der a ⁻ ⟧ (fun _ => c) = (fun _ => 0).
Proof.
  intros c a. apply limit_left_eq with (f1 := fun h => 0).
  - exists 1. split; [ lra | ]. intros x H1. solve_R.
  - apply limit_left_const.
Qed.

Theorem derivative_const : forall c,
  ⟦ der ⟧ (fun _ => c) = (fun _ => 0).
Proof.
  intros c a. apply derivative_at_const.
Qed.

Theorem derivative_on_const : forall c D,
  differentiable_domain D ->
  ⟦ der ⟧ (fun _ => c) D = (fun _ => 0).
Proof.
  intros c D H1.
  apply derivative_imp_derivative_on; auto.
  apply derivative_const.
Qed.

Lemma derivative_on_const_open : forall c a b,
  a < b ->
  ⟦ der ⟧ (fun _ => c) (a, b) = (fun _ => 0).
Proof.
  intros c a b H1.
  apply derivative_on_const.
  apply differentiable_domain_open; auto.
Qed.

Lemma derivative_on_const_closed : forall c a b,
  a < b ->
  ⟦ der ⟧ (fun _ => c) [a, b] = (fun _ => 0).
Proof.
  intros c a b H1.
  apply derivative_on_const.
  apply differentiable_domain_closed; auto.
Qed.

Lemma derivative_at_id : forall a,
  ⟦ der a ⟧ (fun x => x) = (fun _ => 1).
Proof.
  intros a. apply limit_eq with (f1 := fun h => 1).
  - exists 1. split; [ lra | ]. intros x H1; solve_R.
  - apply limit_const.
Qed.

Lemma derivative_at_right_id : forall a,
  ⟦ der a ⁺ ⟧ (fun x => x) = (fun _ => 1).
Proof.
  intros a. apply limit_right_eq with (f1 := fun h => 1).
  - exists 1. split; [ lra | ]. intros x H1; solve_R.
  - apply limit_right_const.
Qed.

Lemma derivative_at_left_id : forall a,
  ⟦ der a ⁻ ⟧ (fun x => x) = (fun _ => 1).
Proof.
  intros a. apply limit_left_eq with (f1 := fun h => 1).
  - exists 1. split; [ lra | ]. intros x H1; solve_R.
  - apply limit_left_const.
Qed.

Theorem derivative_id :
  ⟦ der ⟧ (fun x => x) = (fun _ => 1).
Proof.
  intros a. apply derivative_at_id.
Qed.

Theorem derivative_on_id : forall D,
  differentiable_domain D ->
  ⟦ der ⟧ (fun x => x) D = (fun _ => 1).
Proof.
  intros D H1.
  apply derivative_imp_derivative_on; auto.
  apply derivative_id.
Qed.

Lemma derivative_on_id_open : forall a b,
  a < b ->
  ⟦ der ⟧ (fun x => x) (a, b) = (fun _ => 1).
Proof.
  intros a b H1.
  apply derivative_on_id.
  apply differentiable_domain_open; auto.
Qed.

Lemma derivative_on_id_closed : forall a b,
  a < b ->
  ⟦ der ⟧ (fun x => x) [a, b] = (fun _ => 1).
Proof.
  intros a b H1.
  apply derivative_on_id.
  apply differentiable_domain_closed; auto.
Qed.

Lemma derivative_at_plus : forall f g f' g' a,
  ⟦ der a ⟧ f = f' -> ⟦ der a ⟧ g = g' ->
  ⟦ der a ⟧ (f + g) = f' + g'.
Proof.
  intros f g f' g' a H1 H2. unfold derivative_at.
  replace (fun h => (f (a + h) + g (a + h) - (f a + g a)) / h) with
  (fun h => (f (a + h) - f a) / h + (g (a + h) - g a) / h) by (extensionality h; nra).
  apply limit_plus; auto.
Qed.

Lemma derivative_at_right_plus : forall f g f' g' a,
  ⟦ der a⁺ ⟧ f = f' -> ⟦ der a⁺ ⟧ g = g' ->
  ⟦ der a⁺ ⟧ (f + g) = f' + g'.
Proof.
  intros f g f' g' a H1 H2. unfold derivative_at_right.
  replace (fun h => (f (a + h) + g (a + h) - (f a + g a)) / h) with
  (fun h => (f (a + h) - f a) / h + (g (a + h) - g a) / h) by (extensionality h; nra).
  apply limit_right_plus; auto.
Qed.

Lemma derivative_at_left_plus : forall f g f' g' a,
  ⟦ der a⁻ ⟧ f = f' -> ⟦ der a⁻ ⟧ g = g' ->
  ⟦ der a⁻ ⟧ (f + g) = f' + g'.
Proof.
  intros f g f' g' a H1 H2. unfold derivative_at_left.
  replace (fun h => (f (a + h) + g (a + h) - (f a + g a)) / h) with
  (fun h => (f (a + h) - f a) / h + (g (a + h) - g a) / h) by (extensionality h; nra).
  apply limit_left_plus; auto.
Qed.

Theorem derivative_plus : forall f g f' g',
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' ->
  ⟦ der ⟧ (f + g) = f' + g'.
Proof.
  intros f g f' g' H1 H2 a. apply derivative_at_plus; auto. 
Qed.

Ltac contradict_interval D a H :=
  exfalso;
  first [ apply (interior_not_endpoint D a H); tauto
        | apply (left_endpoint_not_interior D a H); tauto
        | apply (right_endpoint_not_interior D a H); tauto
        | apply (left_endpoint_not_right_endpoint D a H); tauto
        | apply (right_endpoint_not_left_endpoint D a H); tauto
        ].

Theorem derivative_on_plus : forall f g f' g' D,
  differentiable_domain D ->
  ⟦ der ⟧ f D = f' -> ⟦ der ⟧ g D = g' ->
  ⟦ der ⟧ (f + g) D = f' + g'.
Proof.
  intros f g f' g' D H1 H2 H3 a H4.
  specialize (H1 a H4) as [H5 | [H5 | H5]];
  specialize (H2 a H4) as [H6 | [H6 | H6]];
  specialize (H3 a H4) as [H7 | [H7 | H7]];
  try (left; split; auto; apply derivative_at_plus; tauto);
  try (right; left; split; auto; apply derivative_at_right_plus; tauto);
  try (right; right; split; auto; apply derivative_at_left_plus; tauto);
  contradict_interval D a H5.
Qed.

Lemma derivative_on_plus_open : forall f g f' g' a b,
  a < b ->
  ⟦ der ⟧ f (a, b) = f' -> ⟦ der ⟧ g (a, b) = g' ->
  ⟦ der ⟧ (f + g) (a, b) = f' + g'.
Proof.
  intros f g f' g' a b H1 H2 H3.
  apply derivative_on_plus; auto.
  apply differentiable_domain_open; auto.
Qed.

Lemma derivative_on_plus_closed : forall f g f' g' a b,
  a < b ->
  ⟦ der ⟧ f [a, b] = f' -> ⟦ der ⟧ g [a, b] = g' ->
  ⟦ der ⟧ (f + g) [a, b] = f' + g'.
Proof.
  intros f g f' g' a b H1 H2 H3.
  apply derivative_on_plus; auto.
  apply differentiable_domain_closed; auto.
Qed.

Lemma derivative_at_minus : forall f g f' g' a,
  ⟦ der a ⟧ f = f' -> ⟦ der a ⟧ g = g' ->
  ⟦ der a ⟧ (f - g) = f' - g'.
Proof.
  intros f g f' g' a H1 H2. unfold derivative_at.
  replace (fun h => (f (a + h) - g (a + h) - (f a - g a)) / h) with
  (fun h => (f (a + h) - f a) / h - (g (a + h) - g a) / h) by (extensionality h; nra).
  apply limit_minus; auto.
Qed.

Lemma derivative_at_right_minus : forall f g f' g' a,
  ⟦ der a⁺ ⟧ f = f' -> ⟦ der a⁺ ⟧ g = g' ->
  ⟦ der a⁺ ⟧ (f - g) = f' - g'.
Proof.
  intros f g f' g' a H1 H2. unfold derivative_at_right.
  replace (fun h => (f (a + h) - g (a + h) - (f a - g a)) / h) with
  (fun h => (f (a + h) - f a) / h - (g (a + h) - g a) / h) by (extensionality h; nra).
  apply limit_right_minus; auto.
Qed.

Lemma derivative_at_left_minus : forall f g f' g' a,
  ⟦ der a⁻ ⟧ f = f' -> ⟦ der a⁻ ⟧ g = g' ->
  ⟦ der a⁻ ⟧ (f - g) = f' - g'.
Proof.
  intros f g f' g' a H1 H2. unfold derivative_at_left.
  replace (fun h => (f (a + h) - g (a + h) - (f a - g a)) / h) with
  (fun h => (f (a + h) - f a) / h - (g (a + h) - g a) / h) by (extensionality h; nra).
  apply limit_left_minus; auto.
Qed.

Theorem derivative_minus : forall f g f' g',
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' ->
  ⟦ der ⟧ (f - g) = f' - g'.
Proof.
  intros f g f' g' H1 H2 a. apply derivative_at_minus; auto. 
Qed.

Theorem derivative_on_minus : forall f g f' g' D,
  differentiable_domain D ->
  ⟦ der ⟧ f D = f' -> ⟦ der ⟧ g D = g' ->
  ⟦ der ⟧ (f - g) D = f' - g'.
Proof.
  intros f g f' g' D H1 H2 H3 a H4.
  specialize (H1 a H4) as [H5 | [H5 | H5]];
  specialize (H2 a H4) as [H6 | [H6 | H6]];
  specialize (H3 a H4) as [H7 | [H7 | H7]];
  try (left; split; auto; apply derivative_at_minus; tauto);
  try (right; left; split; auto; apply derivative_at_right_minus; tauto);
  try (right; right; split; auto; apply derivative_at_left_minus; tauto);
  contradict_interval D a H5.
Qed.

Lemma derivative_on_minus_open : forall f g f' g' a b,
  a < b ->
  ⟦ der ⟧ f (a, b) = f' -> ⟦ der ⟧ g (a, b) = g' ->
  ⟦ der ⟧ (f - g) (a, b) = f' - g'.
Proof.
  intros f g f' g' a b H1 H2 H3.
  apply derivative_on_minus; auto.
  apply differentiable_domain_open; auto.
Qed.

Lemma derivative_on_minus_closed : forall f g f' g' a b,
  a < b ->
  ⟦ der ⟧ f [a, b] = f' -> ⟦ der ⟧ g [a, b] = g' ->
  ⟦ der ⟧ (f - g) [a, b] = f' - g'.
Proof.
  intros f g f' g' a b H1 H2 H3.
  apply derivative_on_minus; auto.
  apply differentiable_domain_closed; auto.
Qed.

Lemma derivative_at_mult : forall f g f' g' a,
  ⟦ der a ⟧ f = f' -> ⟦ der a ⟧ g = g' ->
  ⟦ der a ⟧ (f ∙ g) = f' ∙ g + f ∙ g'.
Proof.
  intros f g f' g' a H1 H2. unfold derivative_at.
  replace (fun h => (f (a + h) * g (a + h) - f a * g a) / h) with
  (fun h => f (a + h) * ((g (a + h) - g a)/h) + ((f (a + h) - f a)/h * g a)) by (extensionality h; nra).
  replace (f' a * g a + f a * g' a) with (f a * g' a + f' a * g a) by lra.
  apply limit_plus.
  - apply limit_mult; auto. assert (continuous_at (λ x : ℝ, f (a + x)) 0) as H3.
    {
       apply differentiable_at_imp_continuous_at. unfold differentiable_at. unfold derivative_at in *. exists (f' a).
       replace ((λ h : ℝ, (f (a + (0 + h)) - f (a + 0)) / h)) with (λ h : ℝ, (f (a + h) - f a) / h).
       2 : { extensionality h. rewrite Rplus_0_l. rewrite Rplus_0_r. reflexivity. }
       auto.
    }
    unfold continuous_at in H3. rewrite Rplus_0_r in H3. auto.
  - apply limit_mult; auto. solve_lim.
Qed.

Lemma derivative_at_right_mult : forall f g f' g' a,
  ⟦ der a ⁺ ⟧ f = f' -> ⟦ der a ⁺ ⟧ g = g' ->
  ⟦ der a ⁺ ⟧ (f ∙ g) = f' ∙ g + f ∙ g'.
Proof.
  intros f g f' g' a H1 H2. unfold derivative_at_right.
  replace (fun h => (f (a + h) * g (a + h) - f a * g a) / h) with
  (fun h => f (a + h) * ((g (a + h) - g a)/h) + ((f (a + h) - f a)/h * g a)) by (extensionality h; nra).
  replace (f' a * g a + f a * g' a) with (f a * g' a + f' a * g a) by lra.
  apply limit_right_plus.
  - apply limit_right_mult; auto. assert (continuous_at_right (λ x : ℝ, f (a + x)) 0) as H3.
    {
      apply differentiable_at_right_imp_continuous_at_right. unfold differentiable_at_right. unfold derivative_at_right in *. exists (f' a).
      replace ((λ h : ℝ, (f (a + (0 + h)) - f (a + 0)) / h)) with (λ h : ℝ, (f (a + h) - f a) / h).
      2 : { extensionality h. rewrite Rplus_0_l. rewrite Rplus_0_r. reflexivity. }
      auto.
    }
    unfold continuous_at_right in H3. rewrite Rplus_0_r in H3. auto.
  - apply limit_right_mult; auto. apply limit_right_const.
Qed.

Lemma derivative_at_left_mult : forall f g f' g' a,
  ⟦ der a ⁻ ⟧ f = f' -> ⟦ der a ⁻ ⟧ g = g' ->
  ⟦ der a ⁻ ⟧ (f ∙ g) = f' ∙ g + f ∙ g'.
Proof.
  intros f g f' g' a H1 H2. unfold derivative_at_left.
  replace (fun h => (f (a + h) * g (a + h) - f a * g a) / h) with
  (fun h => f (a + h) * ((g (a + h) - g a)/h) + ((f (a + h) - f a)/h * g a)) by (extensionality h; nra).
  replace (f' a * g a + f a * g' a) with (f a * g' a + f' a * g a) by lra.
  apply limit_left_plus.
  - apply limit_left_mult; auto. assert (continuous_at_left (λ x : ℝ, f (a + x)) 0) as H3.
    {
      apply differentiable_at_left_imp_continuous_at_left. unfold differentiable_at_left. unfold derivative_at_left in *. exists (f' a).
      replace ((λ h : ℝ, (f (a + (0 + h)) - f (a + 0)) / h)) with (λ h : ℝ, (f (a + h) - f a) / h).
      2 : { extensionality h. rewrite Rplus_0_l. rewrite Rplus_0_r. reflexivity. }
      auto.
    }
    unfold continuous_at_left in H3. rewrite Rplus_0_r in H3. auto.
  - apply limit_left_mult; auto. apply limit_left_const.
Qed.

Theorem derivative_mult : forall f g f' g',
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' ->
  ⟦ der ⟧ (f ∙ g) = f' ∙ g + f ∙ g'.
Proof.
  intros f g f' g' H1 H2 a. apply derivative_at_mult; auto. 
Qed.

Theorem derivative_on_mult : forall f g f' g' D,
  differentiable_domain D ->
  ⟦ der ⟧ f D = f' -> ⟦ der ⟧ g D = g' ->
  ⟦ der ⟧ (f ∙ g) D = f' ∙ g + f ∙ g'.
Proof.
  intros f g f' g' D H1 H2 H3 a H4.
  specialize (H1 a H4) as [H5 | [H5 | H5]];
  specialize (H2 a H4) as [H6 | [H6 | H6]];
  specialize (H3 a H4) as [H7 | [H7 | H7]];
  try (left; split; auto; apply derivative_at_mult; tauto);
  try (right; left; split; auto; apply derivative_at_right_mult; tauto);
  try (right; right; split; auto; apply derivative_at_left_mult; tauto);
  contradict_interval D a H5.
Qed.

Lemma derivative_on_mult_open : forall f g f' g' a b,
  a < b ->
  ⟦ der ⟧ f (a, b) = f' -> ⟦ der ⟧ g (a, b) = g' ->
  ⟦ der ⟧ (f ∙ g) (a, b) = f' ∙ g + f ∙ g'.
Proof.
  intros f g f' g' a b H1 H2 H3.
  apply derivative_on_mult; auto.
  apply differentiable_domain_open; auto.
Qed.

Lemma derivative_on_mult_closed : forall f g f' g' a b,
  a < b ->
  ⟦ der ⟧ f [a, b] = f' -> ⟦ der ⟧ g [a, b] = g' ->
  ⟦ der ⟧ (f ∙ g) [a, b] = f' ∙ g + f ∙ g'.
Proof.
  intros f g f' g' a b H1 H2 H3.
  apply derivative_on_mult; auto.
  apply differentiable_domain_closed; auto.
Qed.

Theorem derivative_at_mult_const_l : forall f f' a c,
  ⟦ der a ⟧ f = f' -> ⟦ der a ⟧ (c * f) = c * f'.
Proof.
  intros f f' a c H1. set (h := fun _ : ℝ => c). set (h' := fun _ : ℝ => 0).
  assert ((c * f)%f = h ∙ f) as H3 by reflexivity. rewrite H3.
  assert (⟦ der a ⟧ h = h') as H4 by (apply derivative_at_const).
  assert (⟦ der a ⟧ (h ∙ f) = h' ∙ f + h ∙ f') as H5.
  { apply derivative_at_mult; auto. }
  replace (c * f')%f with (h' ∙ f + h ∙ f')%f. 2 : { extensionality x. unfold h, h'. lra. }
  auto.
Qed.

Lemma derivative_at_right_mult_const_l : forall f f' a c,
  ⟦ der a ⁺ ⟧ f = f' -> ⟦ der a ⁺ ⟧ (c * f) = c * f'.
Proof.
  intros f f' a c H1. set (h := fun _ : ℝ => c). set (h' := fun _ : ℝ => 0).
  assert ((c * f)%f = h ∙ f) as H3 by reflexivity. rewrite H3.
  assert (⟦ der a ⁺ ⟧ h = h') as H4 by (apply derivative_at_right_const).
  assert (⟦ der a ⁺ ⟧ (h ∙ f) = h' ∙ f + h ∙ f') as H5.
  { apply derivative_at_right_mult; auto. }
  replace (c * f')%f with (h' ∙ f + h ∙ f')%f. 2 : { extensionality x. unfold h, h'. lra. }
  auto.
Qed.

Lemma derivative_at_left_mult_const_l : forall f f' a c,
  ⟦ der a ⁻ ⟧ f = f' -> ⟦ der a ⁻ ⟧ (c * f) = c * f'.
Proof.
  intros f f' a c H1. set (h := fun _ : ℝ => c). set (h' := fun _ : ℝ => 0).
  assert ((c * f)%f = h ∙ f) as H3 by reflexivity. rewrite H3.
  assert (⟦ der a ⁻ ⟧ h = h') as H4 by (apply derivative_at_left_const).
  assert (⟦ der a ⁻ ⟧ (h ∙ f) = h' ∙ f + h ∙ f') as H5.
  { apply derivative_at_left_mult; auto. }
  replace (c * f')%f with (h' ∙ f + h ∙ f')%f. 2 : { extensionality x. unfold h, h'. lra. }
  auto.
Qed.

Theorem derivative_mult_const_l : forall f f' c,
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ (c * f) = c * f'.
Proof.
  intros f f' c H1 a. apply derivative_at_mult_const_l; auto.
Qed.

Theorem derivative_on_mult_const_l : forall f f' D c,
  differentiable_domain D ->
  ⟦ der ⟧ f D = f' -> ⟦ der ⟧ (c * f) D = c * f'.
Proof.
  intros f f' D c H1 H2 a H3.
  specialize (H1 a H3) as [H4 | [H4 | H4]];
  specialize (H2 a H3) as [H5 | [H5 | H5]];
  try (left; split; auto; apply derivative_at_mult_const_l; tauto);
  try (right; left; split; auto; apply derivative_at_right_mult_const_l; tauto);
  try (right; right; split; auto; apply derivative_at_left_mult_const_l; tauto);
  contradict_interval D a H4.
Qed.

Lemma derivative_on_mult_const_l_open : forall f f' a b c,
  a < b ->
  ⟦ der ⟧ f (a, b) = f' -> ⟦ der ⟧ (c * f) (a, b) = c * f'.
Proof.
  intros f f' a b c H1 H2.
  apply derivative_on_mult_const_l; auto.
  apply differentiable_domain_open; auto.
Qed.

Lemma derivative_on_mult_const_l_closed : forall f f' a b c,
  a < b ->
  ⟦ der ⟧ f [a, b] = f' -> ⟦ der ⟧ (c * f) [a, b] = c * f'.
Proof.
  intros f f' a b c H1 H2.
  apply derivative_on_mult_const_l; auto.
  apply differentiable_domain_closed; auto.
Qed.

Lemma derivative_at_mult_const_r : forall f f' a c,
  ⟦ der a ⟧ f = f' -> ⟦ der a ⟧ (fun x => f x * c) = (fun x => f' x * c).
Proof.
  intros f f' a c H1.
  replace (fun x => f x * c) with (c * f)%f by (extensionality x; lra).
  replace (fun x => f' x * c) with (c * f')%f by (extensionality x; lra).
  apply derivative_at_mult_const_l; auto.
Qed.

Lemma derivative_at_right_mult_const_r : forall f f' a c,
  ⟦ der a ⁺ ⟧ f = f' -> ⟦ der a ⁺ ⟧ (fun x => f x * c) = (fun x => f' x * c).
Proof.
  intros f f' a c H1.
  replace (fun x => f x * c) with (c * f)%f by (extensionality x; lra).
  replace (fun x => f' x * c) with (c * f')%f by (extensionality x; lra).
  apply derivative_at_right_mult_const_l; auto.
Qed.

Lemma derivative_at_left_mult_const_r : forall f f' a c,
  ⟦ der a ⁻ ⟧ f = f' -> ⟦ der a ⁻ ⟧ (fun x => f x * c) = (fun x => f' x * c).
Proof.
  intros f f' a c H1.
  replace (fun x => f x * c) with (c * f)%f by (extensionality x; lra).
  replace (fun x => f' x * c) with (c * f')%f by (extensionality x; lra).
  apply derivative_at_left_mult_const_l; auto.
Qed.

Theorem derivative_mult_const_r : forall f f' c,
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ (fun x => f x * c) = (fun x => f' x * c).
Proof.
  intros f f' c H1.
  replace (fun x => f x * c) with (c * f)%f by (extensionality x; lra).
  replace (fun x => f' x * c) with (c * f')%f by (extensionality x; lra).
  apply derivative_mult_const_l; auto.
Qed.

Theorem derivative_on_mult_const_r : forall f f' D c,
  differentiable_domain D ->
  ⟦ der ⟧ f D = f' -> ⟦ der ⟧ (fun x => f x * c) D = (fun x => f' x * c).
Proof.
  intros f f' D c H1 H2.
  replace (fun x => f x * c) with (c * f)%f by (extensionality x; lra).
  replace (fun x => f' x * c) with (c * f')%f by (extensionality x; lra).
  apply derivative_on_mult_const_l; auto.
Qed.

Lemma derivative_on_mult_const_r_open : forall f f' a b c,
  a < b ->
  ⟦ der ⟧ f (a, b) = f' -> ⟦ der ⟧ (fun x => f x * c) (a, b) = (fun x => f' x * c).
Proof.
  intros f f' a b c H1 H2.
  replace (fun x => f x * c) with (c * f)%f by (extensionality x; lra).
  replace (fun x => f' x * c) with (c * f')%f by (extensionality x; lra).
  apply derivative_on_mult_const_l; auto.
  apply differentiable_domain_open; auto.
Qed.

Lemma derivative_on_mult_const_r_closed : forall f f' a b c,
  a < b ->
  ⟦ der ⟧ f [a, b] = f' -> ⟦ der ⟧ (fun x => f x * c) [a, b] = (fun x => f' x * c).
Proof.
  intros f f' a b c H1 H2.
  replace (fun x => f x * c) with (c * f)%f by (extensionality x; lra).
  replace (fun x => f' x * c) with (c * f')%f by (extensionality x; lra).
  apply derivative_on_mult_const_l; auto.
  apply differentiable_domain_closed; auto.
Qed.

Lemma derivative_at_neg : forall f f' a,
  ⟦ der a ⟧ f = f' -> ⟦ der a ⟧ (fun x => - (f x)) = (fun x => - (f' x)).
Proof.
  intros f f' a H1. replace (- f)%f with ((fun _ => 0) - (fun y => f y))%f by (extensionality y; nra).
  replace (- f')%f with ((fun _ => 0) - (fun y => f' y))%f by (extensionality y; nra).
  apply derivative_at_minus; auto. apply derivative_at_const.
Qed.

Lemma derivative_at_right_neg : forall f f' a,
  ⟦ der a ⁺ ⟧ f = f' -> ⟦ der a ⁺ ⟧ (fun x => - (f x)) = (fun x => - (f' x)).
Proof.
  intros f f' a H1. replace (fun x => - (f x)) with ((fun _ => 0) - f)%f by (extensionality y; nra).
  replace (fun x => - (f' x)) with ((fun _ => 0) - f')%f by (extensionality y; nra).
  apply derivative_at_right_minus; auto. apply derivative_at_right_const.
Qed.

Lemma derivative_at_left_neg : forall f f' a,
  ⟦ der a ⁻ ⟧ f = f' -> ⟦ der a ⁻ ⟧ (fun x => - (f x)) = (fun x => - (f' x)).
Proof.
  intros f f' a H1. replace (fun x => - (f x)) with ((fun _ => 0) - f)%f by (extensionality y; nra).
  replace (fun x => - (f' x)) with ((fun _ => 0) - f')%f by (extensionality y; nra).
  apply derivative_at_left_minus; auto. apply derivative_at_left_const.
Qed.

Theorem derivative_neg : forall f f',
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ (fun x => - (f x)) = (fun x => - (f' x)).
Proof.
  intros f f' H1 a. apply derivative_at_neg; auto.
Qed.

Theorem derivative_on_neg : forall f f' D,
  differentiable_domain D ->
  ⟦ der ⟧ f D = f' -> ⟦ der ⟧ (fun x => - (f x)) D = (fun x => - (f' x)).
Proof.
  intros f f' D H1 H2.
  replace (fun x => - (f x)) with ((fun _ => 0) - f)%f by (extensionality y; nra).
  replace (fun x => - (f' x)) with ((fun _ => 0) - f')%f by (extensionality y; nra).
  apply derivative_on_minus; auto. apply derivative_on_const; auto.
Qed.

Lemma derivative_on_neg_open : forall f f' a b,
  a < b ->
  ⟦ der ⟧ f (a, b) = f' -> ⟦ der ⟧ (fun x => - (f x)) (a, b) = (fun x => - (f' x)).
Proof.
  intros f f' a b H1 H2.
  apply derivative_on_neg; auto.
  apply differentiable_domain_open; auto.
Qed.

Lemma derivative_on_neg_closed : forall f f' a b,
  a < b ->
  ⟦ der ⟧ f [a, b] = f' -> ⟦ der ⟧ (fun x => - (f x)) [a, b] = (fun x => - (f' x)).
Proof.
  intros f f' a b H1 H2.
  apply derivative_on_neg; auto.
  apply differentiable_domain_closed; auto.
Qed.

Lemma derivative_at_pow : forall a n,
  ⟦ der a ⟧ (fun x => x ^ n) = (fun x => INR n * x ^ (n - 1)).
Proof.
  intros a n. induction n as [| k IH].
  - simpl. rewrite Rmult_0_l. apply derivative_at_const.
  - replace (λ x : ℝ, (x ^ S k)%R) with (λ x : ℝ, (x * x ^ k)) by (extensionality x; reflexivity).
    replace (λ x : ℝ, INR (S k) * x ^ (S k - 1))%R with (λ x : ℝ, 1 * x^k + x * (INR k * x^(k-1))).
    2 : { 
      extensionality x. replace (S k - 1)%nat with k by lia. solve_R. replace (x * INR k * x ^ (k - 1)) with (INR k * x^k).
      2 : { 
        replace (x * INR k * x ^ (k - 1)) with (INR k * (x * x ^ (k - 1))) by lra. rewrite tech_pow_Rmult.
        destruct k; solve_R. rewrite Nat.sub_0_r. reflexivity. 
      } solve_R. 
    }
    apply derivative_at_mult; auto. apply derivative_at_id.
Qed.

Lemma derivative_at_right_pow : forall a n,
  ⟦ der a ⁺ ⟧ (fun x => x ^ n) = (fun x => INR n * x ^ (n - 1)).
Proof.
  intros a n. induction n as [| k IH].
  - simpl. rewrite Rmult_0_l. apply derivative_at_right_const.
  - replace (λ x : ℝ, (x ^ S k)%R) with (λ x : ℝ, (x * x ^ k)) by (extensionality x; reflexivity).
    replace (λ x : ℝ, INR (S k) * x ^ (S k - 1))%R with (λ x : ℝ, 1 * x^k + x * (INR k * x^(k-1))).
    2 : { 
      extensionality x. replace (S k - 1)%nat with k by lia. solve_R. replace (x * INR k * x ^ (k - 1)) with (INR k * x^k).
      2 : { 
        replace (x * INR k * x ^ (k - 1)) with (INR k * (x * x ^ (k - 1))) by lra. rewrite tech_pow_Rmult.
        destruct k; solve_R. rewrite Nat.sub_0_r. reflexivity. 
      } solve_R. 
    }
    apply derivative_at_right_mult; auto. apply derivative_at_right_id.
Qed.

Lemma derivative_at_left_pow : forall a n,
  ⟦ der a ⁻ ⟧ (fun x => x ^ n) = (fun x => INR n * x ^ (n - 1)).
Proof.
  intros a n. induction n as [| k IH].
  - simpl. rewrite Rmult_0_l. apply derivative_at_left_const.
  - replace (λ x : ℝ, (x ^ S k)%R) with (λ x : ℝ, (x * x ^ k)) by (extensionality x; reflexivity).
    replace (λ x : ℝ, INR (S k) * x ^ (S k - 1))%R with (λ x : ℝ, 1 * x^k + x * (INR k * x^(k-1))).
    2 : { 
      extensionality x. replace (S k - 1)%nat with k by lia. solve_R. replace (x * INR k * x ^ (k - 1)) with (INR k * x^k).
      2 : { 
        replace (x * INR k * x ^ (k - 1)) with (INR k * (x * x ^ (k - 1))) by lra. rewrite tech_pow_Rmult.
        destruct k; solve_R. rewrite Nat.sub_0_r. reflexivity. 
      } solve_R. 
    }
    apply derivative_at_left_mult; auto. apply derivative_at_left_id.
Qed.

Theorem derivative_pow : forall n,
  ⟦ der ⟧ (fun x => x ^ n) = (fun x => INR n * x ^ (n - 1)).
Proof.
  intros n a. apply derivative_at_pow.
Qed.

Theorem derivative_on_pow : forall n D,
  differentiable_domain D ->
  ⟦ der ⟧ (fun x => x ^ n) D = (fun x => INR n * x ^ (n - 1)).
Proof.
  intros n D H1.
  apply derivative_imp_derivative_on; auto.
  apply derivative_pow.
Qed.

Lemma derivative_on_pow_open : forall n a b,
  a < b ->
  ⟦ der ⟧ (fun x => x ^ n) (a, b) = (fun x => INR n * x ^ (n - 1)).
Proof.
  intros n a b H1.
  apply derivative_on_pow; auto.
  apply differentiable_domain_open; auto.
Qed.

Lemma derivative_on_pow_closed : forall n a b,
  a < b ->
  ⟦ der ⟧ (fun x => x ^ n) [a, b] = (fun x => INR n * x ^ (n - 1)).
Proof.
  intros n a b H1.
  apply derivative_on_pow; auto.
  apply differentiable_domain_closed; auto.
Qed.

Theorem derivative_at_inv : forall f f' a,
  ⟦ der a ⟧ f = f' -> f a <> 0 -> ⟦ der a ⟧ (fun x => / f x) = (fun x => -1 * f' x) / (fun x => f x ^ 2).
Proof.
  intros f f' a H1 H2. unfold derivative_at. 
  assert (H3 : continuous_at f a). { apply differentiable_at_imp_continuous_at. unfold differentiable_at. exists (f' a). auto. }
  pose proof continuous_at_locally_nonzero f a H3 H2 as [δ [H4 H5]].
  apply limit_eq with (f1 := fun h => ((-1 * (f (a + h) - f a) / h)) * (1 / (f a * f (a + h)))).
  { exists δ. split; auto. intros x H6. specialize (H5 (a + x) ltac:(solve_R)). solve_R. }
  apply limit_mult. replace ((λ x : ℝ, -1 * (f (a + x) - f a) / x)) with ((fun x => -1) ∙ (fun x => (f (a + x) - f a) / x)).
  2 : { extensionality x. lra. } apply limit_mult; auto. apply limit_const. apply limit_inv; solve_R.
  apply limit_mult. apply limit_const. rewrite Rmult_1_r. 
  pose proof continuous_at_comp f (fun x => a + x) 0 as H6.
  unfold continuous_at in H6.
  unfold compose in H6.
  rewrite Rplus_0_r in H6. apply H6; solve_lim.
Qed.

Lemma derivative_at_right_inv : forall f f' a,
  ⟦ der a ⁺ ⟧ f = f' -> f a <> 0 -> ⟦ der a ⁺ ⟧ (fun x => / f x) = (fun x => -1 * f' x) / (fun x => f x ^ 2).
Proof.
  intros f f' a H1 H2. unfold derivative_at_right.
  assert (H3 : continuous_at_right f a). { apply differentiable_at_right_imp_continuous_at_right. unfold differentiable_at_right. exists (f' a). auto. }
  pose proof continuous_at_right_locally_nonzero f a H3 H2 as [δ [H4 H5]].
  apply limit_right_eq with (f1 := fun h => ((-1 * (f (a + h) - f a) / h)) * (1 / (f a * f (a + h)))).
  { exists δ. split; auto. intros x H6. specialize (H5 (a + x) ltac:(solve_R)). solve_R. }
  apply limit_right_mult. replace ((λ x : ℝ, -1 * (f (a + x) - f a) / x)) with ((fun x => -1) ∙ (fun x => (f (a + x) - f a) / x)).
  2 : { extensionality x. lra. } apply limit_right_mult; auto. apply limit_right_const. apply limit_right_inv; solve_R.
  apply limit_right_mult. apply limit_right_const. rewrite Rmult_1_r.
  unfold continuous_at_right in H3.
  intros ε H6.
  specialize (H3 ε H6) as [d [Hd1 Hd2]].
  exists d. split; auto.
  intros x H7.
  apply Hd2.
  solve_R.
Qed.

Lemma derivative_at_left_inv : forall f f' a,
  ⟦ der a ⁻ ⟧ f = f' -> f a <> 0 -> ⟦ der a ⁻ ⟧ (fun x => / f x) = (fun x => -1 * f' x) / (fun x => f x ^ 2).
Proof.
  intros f f' a H1 H2. unfold derivative_at_left.
  assert (H3 : continuous_at_left f a). { apply differentiable_at_left_imp_continuous_at_left. unfold differentiable_at_left. exists (f' a). auto. }
  pose proof continuous_at_left_locally_nonzero f a H3 H2 as [δ [H4 H5]].
  apply limit_left_eq with (f1 := fun h => ((-1 * (f (a + h) - f a) / h)) * (1 / (f a * f (a + h)))).
  { exists δ. split; auto. intros x H6. specialize (H5 (a + x) ltac:(solve_R)). solve_R. }
  apply limit_left_mult. replace ((λ x : ℝ, -1 * (f (a + x) - f a) / x)) with ((fun x => -1) ∙ (fun x => (f (a + x) - f a) / x)).
  2 : { extensionality x. lra. } apply limit_left_mult; auto. apply limit_left_const. apply limit_left_inv; solve_R.
  apply limit_left_mult. apply limit_left_const. rewrite Rmult_1_r.
  unfold continuous_at_left in H3.
  intros ε H6.
  specialize (H3 ε H6) as [d [Hd1 Hd2]].
  exists d. split; auto.
  intros x H7.
  apply Hd2.
  solve_R.
Qed.

Theorem derivative_inv : forall f f',
  (forall x, f x <> 0) ->
  ⟦ der ⟧ f = f' -> 
  ⟦ der ⟧ (fun x => / f x) = (fun x => -1 * f' x) / (fun x => f x ^ 2).
Proof.
  intros f f' H1 H2 a.
  apply derivative_at_inv; auto.
Qed.

Theorem derivative_on_inv : forall f f' D,
  differentiable_domain D ->
  (forall x, x ∈ D -> f x <> 0) ->
  ⟦ der ⟧ f D = f' -> 
  ⟦ der ⟧ (fun x => / f x) D = (fun x => -1 * f' x) / (fun x => f x ^ 2).
Proof.
  intros f f' D H1 H2 H3 a H4.
  specialize (H1 a H4) as [H5 | [H5 | H5]];
  specialize (H3 a H4) as [H6 | [H6 | H6]];
  try (left; split; auto; apply derivative_at_inv; [tauto | apply H2; auto]);
  try (right; left; split; auto; apply derivative_at_right_inv; [tauto | apply H2; auto]);
  try (right; right; split; auto; apply derivative_at_left_inv; [tauto | apply H2; auto]);
  contradict_interval D a H5.
Qed.

Lemma derivative_on_inv_open : forall f f' a b,
  a < b ->
  (forall x, a < x < b -> f x <> 0) ->
  ⟦ der ⟧ f (a, b) = f' -> 
  ⟦ der ⟧ (fun x => / f x) (a, b) = (fun x => -1 * f' x) / (fun x => f x ^ 2).
Proof.
  intros f f' a b H1 H2 H3.
  apply derivative_on_inv; auto.
  apply differentiable_domain_open; auto.
Qed.

Lemma derivative_on_inv_closed : forall f f' a b,
  a < b ->
  (forall x, a <= x <= b -> f x <> 0) ->
  ⟦ der ⟧ f [a, b] = f' -> 
  ⟦ der ⟧ (fun x => / f x) [a, b] = (fun x => -1 * f' x) / (fun x => f x ^ 2).
Proof.
  intros f f' a b H1 H2 H3.
  apply derivative_on_inv; auto.
  apply differentiable_domain_closed; auto.   
Qed.

Lemma derivative_at_div : forall f f' g g' a,
  ⟦ der a ⟧ f = f' -> ⟦ der a ⟧ g = g' -> g a <> 0 -> ⟦ der a ⟧ (f / g) = (g ∙ f' - f ∙ g')%f / (g ∙ g).
Proof.
  intros f f' g g' a H1 H2 H3.
  replace (f / g)%f with (f ∙ (fun x => / g x))%f. 2 : { extensionality x. unfold Rdiv. reflexivity. }
  replace (λ x : ℝ, (g x * f' x - f x * g' x) / (g x * g x)) with (fun x => f' x * /g x + (f x * ((-1 * g' x) * / (g x)^2))).
  2 : { extensionality x. assert (g x = 0 \/ g x <> 0) as [H4 | H4] by lra. rewrite H4. simpl. unfold Rdiv. repeat rewrite Rmult_0_l. rewrite Rinv_0. nra. field; lra. }
  apply derivative_at_mult; auto. apply derivative_at_inv; auto.
Qed.

Lemma derivative_at_right_div : forall f f' g g' a,
  ⟦ der a ⁺ ⟧ f = f' -> ⟦ der a ⁺ ⟧ g = g' -> g a <> 0 -> ⟦ der a ⁺ ⟧ (f / g) = (g ∙ f' - f ∙ g')%f / (g ∙ g).
Proof.
  intros f f' g g' a H1 H2 H3.
  replace (f / g)%f with (f ∙ (fun x => / g x))%f. 2 : { extensionality x. unfold Rdiv. reflexivity. }
  replace (λ x : ℝ, (g x * f' x - f x * g' x) / (g x * g x)) with (fun x => f' x * /g x + (f x * ((-1 * g' x) * / (g x)^2))).
  2 : { extensionality x. assert (g x = 0 \/ g x <> 0) as [H4 | H4] by lra. rewrite H4. simpl. unfold Rdiv. repeat rewrite Rmult_0_l. rewrite Rinv_0. nra. field; lra. }
  apply derivative_at_right_mult; auto. apply derivative_at_right_inv; auto.
Qed.

Lemma derivative_at_left_div : forall f f' g g' a,
  ⟦ der a ⁻ ⟧ f = f' -> ⟦ der a ⁻ ⟧ g = g' -> g a <> 0 -> ⟦ der a ⁻ ⟧ (f / g) = (g ∙ f' - f ∙ g')%f / (g ∙ g).
Proof.
  intros f f' g g' a H1 H2 H3.
  replace (f / g)%f with (f ∙ (fun x => / g x))%f. 2 : { extensionality x. unfold Rdiv. reflexivity. }
  replace (λ x : ℝ, (g x * f' x - f x * g' x) / (g x * g x)) with (fun x => f' x * /g x + (f x * ((-1 * g' x) * / (g x)^2))).
  2 : { extensionality x. assert (g x = 0 \/ g x <> 0) as [H4 | H4] by lra. rewrite H4. simpl. unfold Rdiv. repeat rewrite Rmult_0_l. rewrite Rinv_0. nra. field; lra. }
  apply derivative_at_left_mult; auto. apply derivative_at_left_inv; auto.
Qed.

Theorem derivative_div : forall f f' g g',
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> (forall x, g x <> 0) -> 
  ⟦ der ⟧ (f / g) = (g ∙ f' - f ∙ g')%f / (g ∙ g).
Proof.
  intros f f' g g' H1 H2 H3 a.
  apply derivative_at_div; auto.
Qed.

Theorem derivative_on_div : forall f f' g g' D,
  differentiable_domain D ->
  ⟦ der ⟧ f D = f' -> ⟦ der ⟧ g D = g' -> (forall x, x ∈ D -> g x <> 0) -> 
  ⟦ der ⟧ (f / g) D = (g ∙ f' - f ∙ g')%f / (g ∙ g).
Proof.
  intros f f' g g' D H1 H2 H3 H4 a H5.
  specialize (H1 a H5) as [H6 | [H6 | H6]];
  specialize (H2 a H5) as [H7 | [H7 | H7]];
  specialize (H3 a H5) as [H8 | [H8 | H8]];
  try (left; split; auto; apply derivative_at_div; [tauto | tauto | apply H4; auto]);
  try (right; left; split; auto; apply derivative_at_right_div; [tauto | tauto | apply H4; auto]);
  try (right; right; split; auto; apply derivative_at_left_div; [tauto | tauto | apply H4; auto]);
  contradict_interval D a H6.
Qed.

Lemma derivative_on_div_open : forall f f' g g' a b,
  a < b ->
  ⟦ der ⟧ f (a, b) = f' -> ⟦ der ⟧ g (a, b) = g' -> (forall x, x ∈ (a, b) -> g x <> 0) ->
  ⟦ der ⟧ (f / g) (a, b) = (g ∙ f' - f ∙ g')%f / (g ∙ g).
Proof.
  intros f f' g g' a b H1 H2 H3 H4.
  apply derivative_on_div; auto.
  apply differentiable_domain_open; auto.
Qed.

Lemma derivative_on_div_closed : forall f f' g g' a b,
  a < b ->
  ⟦ der ⟧ f [a, b] = f' -> ⟦ der ⟧ g [a, b] = g' -> (forall x, x ∈ [a, b] -> g x <> 0) ->
  ⟦ der ⟧ (f / g) [a, b] = (g ∙ f' - f ∙ g')%f / (g ∙ g).
Proof.
  intros f f' g g' a b H1 H2 H3 H4.
  apply derivative_on_div; auto.
  apply differentiable_domain_closed; auto.
Qed.

Lemma derivative_at_comp : forall f g f' g' a,
  ⟦ der a ⟧ f = f' -> ⟦ der (f a) ⟧ g = g' -> ⟦ der a ⟧ (g ∘ f) = (g' ∘ f)%f ∙ f'.
Proof.
  intros f g f' g' a H1 H2.
  set ( φ := fun h : ℝ => match (Req_dec_T (f (a + h) - f a) 0) with 
                          | left _ => g' (f a)
                          | right _ => (g (f (a + h)) - g (f a)) / (f (a + h) - f a)
                          end).
  assert (continuous_at φ 0) as H3.
  {
    intros ε H4. specialize (H2 ε H4) as [δ' [H5 H6]].  unfold φ. rewrite Rplus_0_r, Rminus_diag.
    assert (H7 : continuous_at f a). 
    { apply differentiable_at_imp_continuous_at. unfold differentiable_at. unfold derivative_at in H1. exists (f' a). auto. }
    specialize (H7 δ' H5) as [δ [H8 H9]]. exists δ. split; auto. intros x H10.
    destruct (Req_dec_T (f (a + x) - f a) 0) as [H11 | H11]; destruct (Req_dec_T 0 0) as [H12 | H12]; try lra; clear H12.
     - solve_R.
     - specialize (H9 (a + x) ltac:(solve_R)). specialize (H6 (f (a + x) - f a) ltac:(solve_R)).
       replace (f a + (f (a + x) - f a)) with (f (a + x)) in H6 by lra. auto.
  }
  unfold continuous_at in H3. unfold derivative_at.
  apply limit_eq with (f1 := fun h => φ h * ((f (a + h) - f a)/h)). 
  2 : { apply limit_mult; auto. unfold φ in H3 at 2. rewrite Rplus_0_r in H3. replace (f a - f a) with 0 in H3 by lra.
         destruct (Req_dec_T 0 0); auto; lra. }
  exists 1. split; try lra.
  intros x H4. unfold φ. unfold compose. destruct (Req_dec_T (f (a + x) - f a) 0) as [H5 | H5]; [ | solve_R].
  rewrite H5. replace (f (a + x)) with (f a) by lra. solve_R.
Qed.

Lemma derivative_at_right_comp : forall f g f' g' a,
  ⟦ der a ⁺ ⟧ f = f' -> ⟦ der (f a) ⟧ g = g' -> ⟦ der a ⁺ ⟧ (g ∘ f) = (g' ∘ f)%f ∙ f'.
Proof.
  intros f g f' g' a H1 H2.
  set ( φ := fun h : ℝ => match (Req_dec_T (f (a + h) - f a) 0) with 
                          | left _ => g' (f a)
                          | right _ => (g (f (a + h)) - g (f a)) / (f (a + h) - f a)
                          end).
  assert (continuous_at_right φ 0) as H3.
  {
    intros ε H4. specialize (H2 ε H4) as [δ' [H5 H6]]. unfold φ. rewrite Rplus_0_r, Rminus_diag.
    assert (H7 : continuous_at_right f a). 
    { apply differentiable_at_right_imp_continuous_at_right. unfold differentiable_at_right. exists (f' a). auto. }
    specialize (H7 δ' H5) as [δ [H8 H9]]. exists δ. split; auto. intros x H10.
    destruct (Req_dec_T (f (a + x) - f a) 0) as [H11 | H11]; destruct (Req_dec_T 0 0) as [H12 | H12]; try lra; clear H12.
      - solve_R.
      - specialize (H9 (a + x) ltac:(solve_R)). specialize (H6 (f (a + x) - f a) ltac:(solve_R)).
        replace (f a + (f (a + x) - f a)) with (f (a + x)) in H6 by lra. auto.
  }
  unfold continuous_at_right in H3. unfold derivative_at_right.
  apply limit_right_eq with (f1 := fun h => φ h * ((f (a + h) - f a)/h)). 
  2 : { apply limit_right_mult; auto. unfold φ in H3 at 2. rewrite Rplus_0_r in H3. replace (f a - f a) with 0 in H3 by lra.
          destruct (Req_dec_T 0 0); auto; lra. }
  exists 1. split; try lra.
  intros x H4. unfold φ. unfold compose. destruct (Req_dec_T (f (a + x) - f a) 0) as [H5 | H5]; [ | solve_R].
  rewrite H5. replace (f (a + x)) with (f a) by lra. solve_R.
Qed.

Lemma derivative_at_left_comp : forall f g f' g' a,
  ⟦ der a ⁻ ⟧ f = f' -> ⟦ der (f a) ⟧ g = g' -> ⟦ der a ⁻ ⟧ (g ∘ f) = (g' ∘ f)%f ∙ f'.
Proof.
  intros f g f' g' a H1 H2.
  set ( φ := fun h : ℝ => match (Req_dec_T (f (a + h) - f a) 0) with 
                          | left _ => g' (f a)
                          | right _ => (g (f (a + h)) - g (f a)) / (f (a + h) - f a)
                          end).
  assert (continuous_at_left φ 0) as H3.
  {
    intros ε H4. specialize (H2 ε H4) as [δ' [H5 H6]]. unfold φ. rewrite Rplus_0_r, Rminus_diag.
    assert (H7 : continuous_at_left f a). 
    { apply differentiable_at_left_imp_continuous_at_left. unfold differentiable_at_left. exists (f' a). auto. }
    specialize (H7 δ' H5) as [δ [H8 H9]]. exists δ. split; auto. intros x H10.
    destruct (Req_dec_T (f (a + x) - f a) 0) as [H11 | H11]; destruct (Req_dec_T 0 0) as [H12 | H12]; try lra; clear H12.
      - solve_R.
      - specialize (H9 (a + x) ltac:(solve_R)). specialize (H6 (f (a + x) - f a) ltac:(solve_R)).
        replace (f a + (f (a + x) - f a)) with (f (a + x)) in H6 by lra. auto.
  }
  unfold continuous_at_left in H3. unfold derivative_at_left.
  apply limit_left_eq with (f1 := fun h => φ h * ((f (a + h) - f a)/h)). 
  2 : { apply limit_left_mult; auto. unfold φ in H3 at 2. rewrite Rplus_0_r in H3. replace (f a - f a) with 0 in H3 by lra.
          destruct (Req_dec_T 0 0); auto; lra. }
  exists 1. split; try lra.
  intros x H4. unfold φ. unfold compose. destruct (Req_dec_T (f (a + x) - f a) 0) as [H5 | H5]; [ | solve_R].
  rewrite H5. replace (f (a + x)) with (f a) by lra. solve_R.
Qed.

Theorem derivative_comp : forall f g f' g',
  ⟦ der ⟧ f = f' -> 
  ⟦ der ⟧ g = g' -> 
  ⟦ der ⟧ (g ∘ f) = (g' ∘ f)%f ∙ f'.
Proof.
  intros f g f' g' H1 H2 a.
  apply derivative_at_comp; auto.
Qed.

Theorem derivative_on_comp : forall f g f' g' D,
  differentiable_domain D ->
  ⟦ der ⟧ f D = f' -> 
  (forall x, x ∈ D -> ⟦ der (f x) ⟧ g = g') ->
  ⟦ der ⟧ (g ∘ f) D = (g' ∘ f)%f ∙ f'.
Proof.
  intros f g f' g' D H1 H2 H3 a H4.
  specialize (H1 a H4) as [H5 | [H5 | H5]];
  specialize (H2 a H4) as [H6 | [H6 | H6]];
  specialize (H3 a H4).
  - destruct H6 as [H6 H7]. left. split; auto. apply derivative_at_comp; auto.
  - destruct H6 as [H6 H7]. exfalso. apply (interior_not_endpoint D a H5). left; auto.
  - destruct H6 as [H6 H7]. exfalso. apply (interior_not_endpoint D a H5). right; auto.
  - destruct H6 as [H6 H7]. exfalso. apply (interior_not_endpoint D a H6). left; auto.
  - destruct H6 as [H6 H7]. right; left. split; auto. apply derivative_at_right_comp; auto.
  - destruct H6 as [H6 H7]. exfalso. apply (left_endpoint_not_right_endpoint D a H5). auto.
  - destruct H6 as [H6 H7]. exfalso. apply (interior_not_endpoint D a H6). right; auto.
  - destruct H6 as [H6 H7]. exfalso. apply (right_endpoint_not_left_endpoint D a H5). auto.
  - destruct H6 as [H6 H7]. right; right. split; auto. apply derivative_at_left_comp; auto.
Qed.

Lemma derivative_on_comp_open : forall f g f' g' a b,
  a < b ->
  ⟦ der ⟧ f (a, b) = f' -> 
  (forall x, x ∈ (a, b) -> ⟦ der (f x) ⟧ g = g') ->
  ⟦ der ⟧ (g ∘ f) (a, b) = (g' ∘ f)%f ∙ f'.
Proof.
  intros f g f' g' a b H1 H2 H3.
  apply derivative_on_comp; auto.
  apply differentiable_domain_open; auto.
Qed.

Lemma derivative_on_comp_closed : forall f g f' g' a b,
  a < b ->
  ⟦ der ⟧ f [a, b] = f' -> 
  (forall x, x ∈ [a, b] -> ⟦ der (f x) ⟧ g = g') ->
  ⟦ der ⟧ (g ∘ f) [a, b] = (g' ∘ f)%f ∙ f'.
Proof.
  intros f g f' g' a b H1 H2 H3.
  apply derivative_on_comp; auto.
  apply differentiable_domain_closed; auto.
Qed.

Definition maximum_point (f: ℝ -> ℝ) (A : Ensemble ℝ) (x : ℝ) :=
  x ∈ A /\ forall y, y ∈ A -> f y <= f x.

Definition minimum_point (f: ℝ -> ℝ) (A : Ensemble ℝ) (x : ℝ) :=
  x ∈ A /\ forall y, y ∈ A -> f x <= f y.

Definition maximum_value (f: ℝ -> ℝ) (A : Ensemble ℝ) (y : ℝ) :=
  exists x, maximum_point f A x /\ y = f x.

Definition minimum_value (f: ℝ -> ℝ) (A : Ensemble ℝ) (y : ℝ) :=
  exists x, minimum_point f A x /\ y = f x.

Definition local_maximum_point (f: ℝ -> ℝ) (A : Ensemble ℝ) (x : ℝ) :=
  x ∈ A /\ ∃ δ, δ > 0 /\ maximum_point f (A ⋂ (x - δ, x + δ)) x.

Definition local_minimum_point (f: ℝ -> ℝ) (A : Ensemble ℝ) (x : ℝ) :=
  x ∈ A /\ ∃ δ, δ > 0 /\ minimum_point f (A ⋂ (x - δ, x + δ)) x.

Lemma continuous_on_interval_attains_min_max : forall f a b,
  a < b -> continuous_on f [a, b] -> exists y1 y2, maximum_value f [a, b] y1 /\ minimum_value f [a, b] y2.
Proof.
  intros f a b H1 H2. 
  pose proof continuous_on_interval_attains_maximum f a b H1 H2 as [x1 [H3 H4]]. 
  pose proof continuous_on_interval_attains_minimum f a b H1 H2 as [x2 [H5 H6]].
  exists (f x1), (f x2). split; unfold minimum_value, minimum_point, maximum_value, maximum_point.
  - exists x1. repeat split; auto. solve_R. solve_R. intros y H7. specialize (H4 y H7). lra.
  - exists x2. repeat split; solve_R.
Qed.

Lemma min_max_equal_imp_const_val : forall f a b y1 y2,
  maximum_value f [a, b] y1 -> minimum_value f [a, b] y2 -> y1 = y2 -> forall x, x ∈ [a, b] -> f x = y1.
Proof.
  intros f a b y1 y2 H1 H2 H3 x H4. 
  destruct H1 as [x1 [[H5 H6] H9]]. subst y1.
  destruct H2 as [x2 [[H7 H8] H10]]. subst y2.
  specialize (H6 x H4). specialize (H8 x H4). lra.
Qed.

Lemma min_max_equal_imp_const : forall f a b y1 y2,
  maximum_value f [a, b] y1 -> minimum_value f [a, b] y2 -> y1 = y2 -> forall x1 x2, x1 ∈ [a, b] -> x2 ∈ [a, b] -> f x1 = f x2.
Proof.
  intros f a b y1 y2 H1 H2 H3 x1 x2 H4 H5. 
  specialize (min_max_equal_imp_const_val f a b y1 y2 H1 H2 H3 x1 H4) as H6.
  specialize (min_max_equal_imp_const_val f a b y1 y2 H1 H2 H3 x2 H5) as H7. 
  lra.
Qed.

Theorem derivative_at_maximum_point_eq_zero : forall f a b x,
  maximum_point f (a, b) x -> differentiable_at f x -> ⟦ der x ⟧ f = (λ _, 0).
Proof.
  intros f a b x [H1 H2] [L H3]. assert (exists δ, 0 < δ /\ forall h, |h| < δ -> f (x + h) - f x <= 0) as [δ1 [H4 H5]].
  { exists (Rmin (b - x) (x - a)). split. solve_R. intros h H4. specialize (H2 (x + h) ltac:(solve_R)). lra. }
  assert (exists δ, 0 < δ /\ forall h, |h| < δ -> h > 0 -> (f (x + h) - f x) / h <= 0) as [δ2 [H6 H7]].
  { exists δ1. split. solve_R. intros h H6 H7. specialize (H5 h ltac:(solve_R)) as [H8 | H8]. apply Rlt_le. apply Rdiv_neg_pos; auto. solve_R. }
  assert (exists δ, 0 < δ /\ forall h, |h| < δ -> h < 0 -> (f (x + h) - f x) / h >= 0) as [δ3 [H8 H9]].
  { exists δ1. split. solve_R. intros h H10 H11. specialize (H5 h ltac:(solve_R)) as [H12 | H12]. apply Rgt_ge. apply Rdiv_neg_neg; auto. solve_R. }
  assert (L = 0 \/ L <> 0) as [H10 | H10] by lra.
  - intros ε H11. specialize (H3 ε H11) as [δ4 [H12 H13]]. exists δ4. split; auto. intros h H14. specialize (H13 h ltac:(solve_R)). solve_R.
  - exfalso. clear H1 H2 a b H4 H5 δ1. specialize (H3 (|L| / 2) ltac:(solve_R)) as [δ4 [H12 H13]]. set (h := Rmin (δ2/2) (Rmin (δ3/2) (δ4/2))).
    assert (h > 0) as H14 by (unfold h; solve_R). assert (-h < 0) as H15 by lra. specialize (H13 h ltac:(unfold h; solve_R)) as H13'. specialize (H13 (-h) ltac:(unfold h; solve_R)).
    specialize (H7 h ltac:(unfold h; solve_R) H14). specialize (H9 (-h) ltac:(unfold h; solve_R) H15). solve_R. 
Qed.

Theorem derivative_at_minimum_point_zero : forall f a b x,
  minimum_point f (a, b) x -> differentiable_at f x -> ⟦ der x ⟧ f = (λ _, 0). 
Proof.
  intros f a b x [H1 H2] [L H3]. 
  pose proof derivative_at_maximum_point_eq_zero (-f) a b x as H4. 
  assert (⟦ der x ⟧ (-f) = (λ _ : ℝ, 0) -> ⟦ der x ⟧ f = (λ _ : ℝ, 0)) as H5.
  {
    intros H5. apply derivative_at_mult_const_l with (c := -1) in H5. 
    replace (-1 * 0) with 0 in H5 by lra.
    replace ((λ x : ℝ, -1 * - f x)) with (λ x : ℝ, f x) in H5. 
    2 : { extensionality x'. lra. } auto.
  }
  apply H5. apply H4; auto. 
  unfold maximum_point. split; auto. intros y H6. specialize (H2 y H6). lra.
  unfold differentiable_at. exists (-1 * L). 
  replace ((λ h : ℝ, (- f (x + h) - - f x) / h)) with ((λ h : ℝ, -1 * ((f (x + h) - f x) / h))).
  2 : { extensionality x'. lra. } apply limit_mult; solve_lim.
Qed.

Theorem derivative_at_local_maximum_point_zero : forall f a b x,
  local_maximum_point f (a, b) x -> differentiable_at f x -> ⟦ der x ⟧ f = (λ _, 0).
Proof.
  intros f a b x [H1 [δ [H2 H3]]] H4. 
  assert (H5 : maximum_point f (( Rmax a (x - δ), Rmin b (x + δ) )) x).
  { split. solve_R. intros y H5. apply H3. 
    replace ((λ x0 : ℝ, a < x0 < b) ⋂ λ x0 : ℝ, x - δ < x0 < x + δ) with (( Rmax a (x - δ), Rmin b (x + δ) )).
    2 : { apply set_equal_def. intros x0. split; intros H6. 
          - split; solve_R. 
          - apply In_Intersection_def in H6 as [H6 H7]. solve_R. }
    solve_R.
  }
  apply derivative_at_maximum_point_eq_zero with (a := Rmax a (x - δ)) (b := Rmin b (x + δ)); auto. 
Qed.

Theorem derivative_at_local_minimum_point_zero : forall f a b x,
  local_minimum_point f (a, b) x -> differentiable_at f x -> ⟦ der x ⟧ f = (λ _, 0).
Proof.
  intros f a b x [H1 [δ [H2 [H3 H4]]]] [L H5]. 
  pose proof derivative_at_local_maximum_point_zero (-f) a b x as H6. 
  assert (⟦ der x ⟧ (-f) = (λ _ : ℝ, 0) -> ⟦ der x ⟧ f = (λ _ : ℝ, 0)) as H7.
  {
    intros H7. apply derivative_at_mult_const_l with (c := -1) in H7. 
    replace (-1 * 0) with 0 in H7 by lra.
    replace ((λ x : ℝ, -1 * - f x)) with (λ x : ℝ, f x) in H7. 
    2 : { extensionality x'. lra. } auto.
  }
  apply H7. apply H6; auto. split; auto. exists δ; split; [auto | split; auto]. 
  intros y H8. specialize (H4 y H8). lra.
  exists (-1 * L). 
  replace ((λ h : ℝ, (- f (x + h) - - f x) / h)) with ((λ h : ℝ, -1 * ((f (x + h) - f x) / h))).
  apply limit_mult; solve_lim. extensionality h. lra.
Qed.

Definition critical_point (f: ℝ -> ℝ) (A : Ensemble ℝ) (x : ℝ) :=
  x ∈ A /\ ⟦ der x ⟧ f = (λ _, 0).

Definition critical_value (f: ℝ -> ℝ) (A : Ensemble ℝ) (y : ℝ) :=
  exists x, critical_point f A x /\ y = f x.

Theorem rolles_theorem : forall f a b,
  a < b -> continuous_on f [a, b] -> differentiable_on f (a, b) -> f a = f b -> exists x, critical_point f (a, b) x.
Proof.
  intros f a b H1 H2 H3 H4. 
  pose proof continuous_on_interval_attains_min_max f a b H1 H2 as [y1 [y2 [H5 H6]]].
  pose proof H5 as H5'. pose proof H6 as H6'. 
  destruct H5' as [x1 [[H7 H8] H9]]. destruct H6' as [x2 [[H10 H11] H12]].
  assert (x1 ∈ (a, b) \/ x2 ∈ (a, b) \/ ((x1 = a \/ x1 = b) /\ (x2 = a \/ x2 = b))) as [H13 | [H13 | [H13 H14]]] by (solve_R).
  - exists x1. split; auto. apply derivative_at_maximum_point_eq_zero with (a := a) (b := b); auto. 
    unfold maximum_point. split; auto. intros y H14. apply H8. solve_R. 
    apply differentiable_on_imp_differentiable_at with (D := (a, b)); auto. apply open_interior_iff; solve_R.
  - exists x2. split; auto. apply derivative_at_minimum_point_zero with (a := a) (b := b); auto. 
    unfold minimum_point. split; auto. intros y H14. apply H11. solve_R. 
    apply differentiable_on_imp_differentiable_at with (D := (a, b)); auto. apply open_interior_iff; solve_R.
  - assert (y1 = y2) as H15. { destruct H13 as [H13 | H13], H14 as [H14 | H14]; subst; auto. }
    pose proof min_max_equal_imp_const f a b y1 y2 H5 H6 H15 as H16. 
    exists ((a + b) / 2). split. solve_R. 
    apply limit_eq with (f1 := (fun x => 0)).
    -- exists ((b - a)/2); split; try lra. intros h H17.
       replace (f ((a + b) / 2 + h)) with (f ((a + b) / 2)).
       2 : { apply H16; solve_R. } 
       lra.
    -- apply limit_const.
Qed.

Theorem mean_value_theorem : forall f a b,
  a < b -> continuous_on f [a, b] -> differentiable_on f (a, b) -> exists x, x ∈ (a, b) /\ ⟦ der x ⟧ f = (λ _, (f b - f a) / (b - a)).
Proof.
  intros f a b H1 H2 H3. set (h := fun x => f x - ((f b - f a) / (b - a)) * (x - a)).
  assert (continuous_on h [a, b]) as H4. 
  { 
    unfold h.
    apply continuous_on_minus; auto.
    apply continuous_on_mult.
    - apply continuous_on_const.
    - apply continuous_on_minus.
      -- apply continuous_on_id.
      -- apply continuous_on_const.
  }
  assert (differentiable_on h (a, b)) as H5.
  {
    intros x. left. destruct (H3 x ltac:(auto)) as [[H6 [L H7]] | [[H6 _] | [H6 H7]]].
    - split; auto. exists (L - (f b - f a) / (b - a)). unfold h.
      apply limit_eq with (f1 := (fun h => (f (x + h) - f x) / h - (f b - f a) / (b - a))).
      exists 1. split; try lra. solve_R.
      apply limit_minus; auto. solve_lim.
    - exfalso. apply (open_not_left_pt a b x); auto.
    - exfalso. apply (open_not_right_pt a b x); auto.
  }
  assert (h a = f a) as H6 by (unfold h; lra).
  assert (h b = f a) as H7 by (unfold h; solve_R).
  pose proof rolles_theorem h a b H1 H4 H5 ltac:(lra) as [x [H8 H9]].
  exists x; split; auto. assert (H10 : ⟦ lim 0 ⟧ (λ h : ℝ, (f (x + h) - f x) / h - (f b - f a) / (b - a)) = 0).
  {
     apply limit_eq with (f1 := (λ h : ℝ, (f(x+h)-(f b-f a)/(b-a)*(x+h-a)-(f x-(f b-f a)/(b-a)*(x-a)))/h)); solve_R.
     exists 1. split; solve_R.
  }
  intros ε H11. specialize (H10 ε H11) as [δ [H12 H13]]. exists δ; split; auto.
  intros x0 H14. specialize (H13 x0 H14). solve_R.
Qed.

Corollary derivative_zero_imp_const : forall f a b, 
  a < b -> ⟦ der ⟧ f [a, b] = (λ _, 0) -> exists c, forall x, x ∈ [a, b] -> f x = c.
Proof.
  intros f a b H1 H2. exists (f a). intros x H3. pose proof classic (x = a) as [H4 | H4]; subst; auto. assert (a < x) as H5. { solve_R. }
  assert (continuous_on f [a, x]) as H6. {
    apply continuous_on_closed_interval_iff; auto; repeat split.
    - intros x0 H6. apply differentiable_at_imp_continuous_at. 
      assert (H7 : x0 ∈ (a, b)). { solve_R. } 
      specialize (H2 x0 ltac:(solve_R)). 
      destruct H2 as [H2 | [H2 | H2]].
      -- destruct H2 as [_ H2]. exists 0; auto.
      -- exfalso. apply (closed_not_left_pt_interior a b x0 H1 H7 ltac:(tauto)).
      -- exfalso. apply (closed_not_right_pt_interior a b x0 H1 H7 ltac:(tauto)).
    - specialize (H2 a ltac:(solve_R)). destruct H2 as [H2 | [H2 | H2]].
      -- exfalso. apply (closed_not_interior_a a b H1 ltac:(tauto)).
      -- apply differentiable_at_right_imp_continuous_at_right. destruct H2 as [_ H2]. unfold differentiable_at_right. exists 0; auto.
      -- exfalso. apply (closed_not_right_pt_a a b H1 ltac:(tauto)).
    - assert (x = b \/ x < b) as [H6 | H6] by (solve_R).
      -- subst. apply differentiable_at_left_imp_continuous_at_left. specialize (H2 b ltac:(solve_R)). destruct H2 as [H2 | [H2 | H2]].
        + exfalso. apply (closed_not_interior_b a b H1 ltac:(tauto)).
        + exfalso. apply (closed_not_left_pt_b a b H1 ltac:(tauto)).
        + destruct H2 as [_ H2]. unfold differentiable_at_left. exists 0; auto. 
      -- apply differentiable_at_left_imp_continuous_at_left. 
         assert (H7 : x ∈ (a, b)). { solve_R. }
         specialize (H2 x ltac:(solve_R)). destruct H2 as [H2 | [H2 | H2]].
        + destruct H2 as [_ H2]. exists 0. apply derivative_at_iff in H2; tauto.
        + exfalso. apply (closed_not_left_pt_interior a b x H1 H7 ltac:(tauto)).
        + exfalso. apply (closed_not_right_pt_interior a b x H1 H7 ltac:(tauto)).
  }
  assert (differentiable_on f (a, x)) as H7.
  {
    intros x0 H7. left. split.
    - apply open_interior_iff; solve_R.
    - assert (H8 : x0 ∈ (a, b)). { solve_R. }
      specialize (H2 x0 ltac:(solve_R)) as [H2 | [H2 | H2]].
      -- destruct H2 as [_ H2]. exists 0. auto.
      -- exfalso. apply (closed_not_left_pt_interior a b x0 H1 H8 ltac:(tauto)).
      -- exfalso. apply (closed_not_right_pt_interior a b x0 H1 H8 ltac:(tauto)).
  }
  pose proof mean_value_theorem f a x H5 H6 H7 as [c [H8 H9]]. specialize (H2 c ltac:(solve_R)). 
  set (f1 := (λ _ : ℝ, (f x - f a) / (x - a))). set (f2 := (λ _ : ℝ, 0)). assert (f1 c = f2 c) as H10.
  {
    destruct H2 as [H2 | [H2 | H2]].
    - apply derivative_at_unique with (f := f); tauto.
    - exfalso. apply (closed_not_left_pt_interior a b c H1); solve_R.
    - exfalso. apply (closed_not_right_pt_interior a b c H1); solve_R.
  } unfold f1, f2 in H10.
  apply Rmult_eq_compat_r with (r := (x - a)) in H10. field_simplify in H10; lra.
Qed.

Corollary corollary_11_2 : forall f f' g g' a b, 
  a < b -> ⟦ der ⟧ f [a, b] = f' -> ⟦ der ⟧ g [a, b] = g' -> (forall x, x ∈ [a, b] -> f' x = g' x) -> exists c, forall x, x ∈ [a, b] -> f x = g x + c.
Proof.
  intros f f' g g' a b H1 H2 H3 H4. set (h := fun x => f x - g x). assert (⟦ der ⟧ h [a, b] = (λ x, f' x - g' x)) as H6.
  {
    intros x0 H6. unfold h. assert (x0 = a \/ x0 = b \/ (x0 > a /\ x0 < b)) as [H7 | [H7 | H7]] by (unfold Ensembles.In in *; lra).
    - right; left. split.
      -- subst. apply closed_left_pt_iff; auto.
      -- specialize (H2 x0 H6) as [H2 | [H2 | H2]]; specialize (H3 x0 H6) as [H3 | [H3 | H3]]; subst;
         try (exfalso; apply (closed_not_interior_a a b H1); tauto); 
         try (exfalso; apply (closed_not_right_pt_a a b H1); tauto); 
         apply derivative_at_right_minus; tauto.
    - right; right. split.
      -- subst. apply closed_right_pt_iff; auto.
      -- specialize (H2 x0 H6) as [H2 | [H2 | H2]]; specialize (H3 x0 H6) as [H3 | [H3 | H3]]; subst;
         try (exfalso; apply (closed_not_interior_b a b H1); tauto); 
         try (exfalso; apply (closed_not_left_pt_b a b H1); tauto); 
         apply derivative_at_left_minus; tauto.
    - left. split.
      -- apply closed_interior_iff; solve_R.
      -- specialize (H2 x0 H6) as [H2 | [H2 | H2]]; specialize (H3 x0 H6) as [H3 | [H3 | H3]];
         try (exfalso; apply (closed_not_left_pt_interior a b x0 H1 H7); tauto);
         try (exfalso; apply (closed_not_right_pt_interior a b x0 H1 H7); tauto);
         apply derivative_at_minus; tauto.
  }
  assert (⟦ der ⟧ h [a, b] = (λ _, 0)) as H7.
  { apply derivative_on_ext with (f1' := (f' - g')%f); auto; try lra. intros x H7. specialize (H4 x H7). lra. }
  apply derivative_zero_imp_const with (a := a) (b := b) in H7 as [c H8]; auto.
  exists c. intros x H9. unfold h. specialize (H8 x H9). unfold h in H8. lra.
Qed.

Definition tangent_line (f f' : R -> R) (a : R) : R -> R :=
  fun x => f' a * (x - a) + f a.

Definition increasing_on (f: ℝ -> ℝ) (A : Ensemble ℝ) :=
  forall a b, a ∈ A -> b ∈ A -> a < b -> f a < f b.

Definition decreasing_on (f: ℝ -> ℝ) (A : Ensemble ℝ) :=
  forall a b, a ∈ A -> b ∈ A -> a < b -> f a > f b.

Definition increasing (f: ℝ -> ℝ) :=
  increasing_on f ℝ.

Definition decreasing (f: ℝ -> ℝ) :=
  decreasing_on f ℝ.

Lemma increasing_on_neg : forall f A,
  increasing_on f A -> decreasing_on (-f) A.
Proof.
  intros f A H1 a b H2 H3 H4. specialize (H1 a b H2 H3 H4). lra.
Qed.

Lemma decreasing_on_neg : forall f A,
  decreasing_on f A -> increasing_on (-f) A.
Proof.
  intros f A H1 a b H2 H3 H4. specialize (H1 a b H2 H3 H4). lra.
Qed.

Lemma nth_differentiable_on_imp_differentiable_at : forall n f D a,
  (n > 0)%nat ->
  a ∈ D -> 
  interior_point D a ->
  nth_differentiable_on n f D -> 
  differentiable_at f a.
Proof.
  intros n f D a H H0 H1 [fn' H2].
  destruct n; [lia|].
  simpl in H2.
  destruct H2 as [f' [H2 H3]].
  specialize (H2 a H0) as [[H4 H5] | [[H4 H5] | [H4 H5]]].
  - exists (f' a). apply H5.
  - exfalso. apply interior_not_endpoint in H1. tauto.
  - exfalso. apply interior_not_endpoint in H1. tauto.
Qed.

Lemma nth_differentiable_on_imp_differentiable_on : forall n f D,
  (n > 0)%nat ->
  nth_differentiable_on n f D -> 
  differentiable_on f D.
Proof.
  intros n f D H [fn' H0].
  destruct n; [lia|].
  simpl in H0.
  destruct H0 as [f' [H0 H1]].
  intros a H2.
  specialize (H0 a H2).
  destruct H0 as [[H3 H4] | [[H3 H4] | [H3 H4]]].
  - left. split; [apply H3 | exists (f' a); apply H4].
  - right; left. split; [apply H3 | exists (f' a); apply H4].
  - right; right. split; [apply H3 | exists (f' a); apply H4].
Qed.

Lemma derivative_on_imp_derivative_at : forall a b x f f',
  a < b -> x ∈ (a, b) -> ⟦ der ⟧ f (a, b) = f' -> ⟦ der x ⟧ f = f'.
Proof.
  intros a b x f f' H1 H2 H3. specialize (H3 x H2) as [[_ H3] | [[H3 _] | [H3 _]]]; auto.
  - apply left_interval_endpoint_open in H3; tauto.
  - apply right_interval_endpoint_open in H3; tauto.
Qed.

Lemma derivative_on_imp_derivative_at' : forall a D f f',
  interior_point D a -> ⟦ der ⟧ f D = f' -> ⟦ der a ⟧ f = f'.
Proof.
  intros a D f f' H1 H2. assert (H3 : a ∈ D). { destruct H1 as [δ [H3 H4]]. specialize (H4 a ltac:(solve_R)). auto. }
   specialize (H2 a H3). destruct H2 as [[_ H2] | [[H2 _] | [H2 _]]]; auto.
  - exfalso. apply (interior_point_not_endpoint D a H1); tauto.
  - exfalso. apply (interior_point_not_endpoint D a H1); tauto.
Qed.
  
Lemma derivative_on_closed_imp_open : forall a b f f',
  ⟦ der ⟧ f [a, b] = f' ->  ⟦ der ⟧ f (a, b) = f'.
Proof.
  intros a b f f' H1 x H2. left. split.
  - apply is_interior_point_open; solve_R.
  - specialize (H1 x ltac:(solve_R)) as [[_ H1] | [[H1 _] | [H1 _]]]; auto.
    -- pose proof not_left_endpoint a b x ltac:(solve_R) ltac:(solve_R) as H3; tauto.
    -- pose proof not_right_endpoint a b x ltac:(solve_R) ltac:(solve_R) as H3; tauto.
Qed.

Lemma derivative_at_eq_f : forall f1 f2 f' c a b,
  a < c < b -> (forall x, a < x < b -> f1 x = f2 x) ->  ⟦ der c ⟧ f1 = f' -> ⟦ der c ⟧ f2 = f'.
Proof.
  intros f1 f2 f' c a b H1 H2 H3 ε H4. specialize (H3 ε H4) as [δ [H3 H5]].
  exists (Rmin (Rmin δ (b - c)) (c - a)); split. solve_R. intros x H6. repeat rewrite <- H2; auto.
  2 : { solve_R. } specialize (H5 x ltac:(solve_R)). auto.
Qed.

Lemma derivative_at_eq_eventually : forall f1 f2 f' c,
  (exists δ, δ > 0 /\ forall x, |x - c| < δ -> f1 x = f2 x) ->
    ⟦ der c ⟧ f1 = f' -> ⟦ der c ⟧ f2 = f'.
Proof.
  intros f1 f2 f' c [δ [H1 H2]] H3.
  apply derivative_at_eq_f with (a := c - δ) (b := c + δ) (f1 := f1).
  - solve_R.
  - intros x H4. apply H2; solve_R.
  - solve_R.
Qed.

Lemma derivative_at_eq_f' : forall f f1' f2' c,
  (forall x, f1' x = f2' x) ->  ⟦ der c ⟧ f = f1' -> ⟦ der c ⟧ f = f2'.
Proof.
  intros f f1' f2' c H1 H2 ε H3. specialize (H2 ε H3) as [δ [H2 H4]].
  exists δ; split; auto. intros x H5. specialize (H4 x H5). rewrite <- H1.
  auto.
Qed.

Lemma derivative_at_eq_f'' : forall f f1' f2' a b c,
  a < c < b -> (forall x, a < x < b -> f1' x = f2' x) -> ⟦ der c ⟧ f = f1' -> ⟦ der c ⟧ f = f2'.
Proof.
  intros f f1' f2' a b c H1 H2 H3 ε H4. specialize (H3 ε H4) as [δ [H3 H5]].
  exists (Rmin (Rmin δ (b - c)) (c - a)); split. solve_R. intros x H6. repeat rewrite <- H2; auto.
  specialize (H5 x ltac:(solve_R)). auto.
Qed.

Lemma derivative_at_right_eq : forall f f1' f2' c,
  (forall x, f1' x = f2' x) ->  ⟦ der c⁺ ⟧ f = f1' -> ⟦ der c⁺ ⟧ f = f2'.
Proof.
  intros f f1' f2' c H1 H2 ε H3. specialize (H2 ε H3) as [δ [H2 H4]].
  exists δ; split; auto. intros x H5. specialize (H4 x H5). rewrite <- H1.
  auto.
Qed.

Lemma derivative_at_left_eq :  forall f f1' f2' c,
  (forall x, f1' x = f2' x) ->  ⟦ der c⁻ ⟧ f = f1' -> ⟦ der c⁻ ⟧ f = f2'.
Proof.
  intros f f1' f2' c H1 H2 ε H3. specialize (H2 ε H3) as [δ [H2 H4]].
  exists δ; split; auto. intros x H5. specialize (H4 x H5). rewrite <- H1.
  auto.
Qed.

Lemma derivative_replace_eq : forall f g f',
  (forall x, f x = g x) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = f'.
Proof.
  intros f g f' H1 H2 x. specialize (H2 x).
  replace g with f in *. 2 : { extensionality x'. apply H1. }
  auto.
Qed.

Lemma derivative_at_replace_eq : forall f g f' a,
  (forall x, f x = g x) -> ⟦ der a ⟧ f = f' -> ⟦ der a ⟧ g = f'.
Proof.
  intros f g f' a H1 H2.
  replace g with f; auto.
  extensionality x. apply H1.
Qed.

Theorem MVT : forall f f' a b,
  a < b -> continuous_on f [a, b] -> ⟦ der ⟧ f (a, b) = f' ->
  exists x, x ∈ (a, b) /\ f' x = (f b - f a) / (b - a).
Proof.
  intros f f' a b H1 H2 H3. pose proof theorem_11_4 f a b H1 H2 as [x [H4 H5]].
  - apply derivative_on_imp_differentiable_on with (f' := f') in H3 as H6; auto.
  - exists x; split; auto. specialize (H3 x ltac:(solve_R)). destruct H3 as [[_ H3] | [[H3 _] | [H3 _]]]; auto.
    -- pose proof derivative_of_function_at_x_unique f f' (fun _ => (f b - f a) / (b - a)) x H3 H5. auto.
    -- exfalso. apply (left_interval_endpoint_open a b x); auto.
    -- exfalso. apply (right_interval_endpoint_open a b x); auto.
Qed.
  
Corollary corollary_11_3_a : forall f f' a b, 
  a < b -> ⟦ der ⟧ f [a, b] = f' -> (forall x, x ∈ [a, b] -> f' x > 0) -> increasing_on f [a, b].
Proof.
  intros f f' a b H1 H2 H3 x1 x2 H4 H5 H6. assert (H7 : continuous_on f [x1, x2]).
  {
    apply continuous_on_closed_interval_subset with (a := a) (b := b); solve_R.
    apply theorem_9_1_d; auto. apply derivative_on_imp_differentiable_on with (f' := f'); auto.
  }
  assert (H8 : differentiable_on f (x1, x2)).
  {
    apply differentiable_on_open_interval_subset with (a := a) (b := b); solve_R.
    apply derivative_on_imp_differentiable_on with (f' := f'); auto. 
  }
  
  pose proof theorem_11_4 f x1 x2 H6 H7 H8 as [x [H9 H10]]. 
  set (h := λ _ : ℝ, (f x2 - f x1) / (x2 - x1)). assert (h x = f' x) as H11.
  {
    apply derivative_of_function_at_x_unique with (f := f); auto. specialize (H2 x ltac:(solve_R)) as [H2 | [H2 | H2]].
    - apply H2.
    - destruct H2 as [H2 _]. apply is_left_endpoint_closed in H2; solve_R.
    - destruct H2 as [H2 _]. apply is_right_endpoint_closed in H2; solve_R.
  }
  specialize (H3 x ltac:(unfold Ensembles.In in *; lra)). unfold h in H11. 
  unfold h in H11. assert (H12 : (f x2 - f x1) / (x2 - x1) > 0) by lra.
  apply Rmult_gt_compat_r with (r := (x2 - x1)) in H12; field_simplify in H12; lra.
Qed.

Corollary corollary_11_3_b : forall f f' a b, 
  a < b -> ⟦ der ⟧ f [a, b] = f' -> (forall x, x ∈ [a, b] -> f' x < 0) -> decreasing_on f [a, b].
Proof.
  intros f f' a b H1 H2 H3 x1 x2 H4 H5 H6. assert (H7 : continuous_on f [x1, x2]).
  {
    apply continuous_on_closed_interval_subset with (a := a) (b := b); solve_R.
    apply theorem_9_1_d; auto. apply derivative_on_imp_differentiable_on with (f' := f'); auto.
  }
  assert (H8 : differentiable_on f (x1, x2)).
  {
    apply differentiable_on_open_interval_subset with (a := a) (b := b); solve_R.
    apply derivative_on_imp_differentiable_on with (f' := f'); auto.
  }
  pose proof theorem_11_4 f x1 x2 H6 H7 H8 as [x [H9 H10]]. 
  set (h := λ _ : ℝ, (f x2 - f x1) / (x2 - x1)). assert (h x = f' x) as H11.
  {
     apply derivative_of_function_at_x_unique with (f := f); auto. specialize (H2 x ltac:(solve_R)) as [H2 | [H2 | H2]].
    - apply H2.
    - destruct H2 as [H2 _]. apply is_left_endpoint_closed in H2; solve_R.
    - destruct H2 as [H2 _]. apply is_right_endpoint_closed in H2; solve_R.
  }
  specialize (H3 x ltac:(unfold Ensembles.In in *; lra)). unfold h in H11. 
  unfold h in H11. assert (H12 : (f x2 - f x1) / (x2 - x1) < 0) by lra.
  apply Rmult_lt_compat_r with (r := (x2 - x1)) in H12; field_simplify in H12; lra.
Qed.

Corollary corollary_11_3_b' : forall f f' a b,
  a < b -> continuous_on f [a, b] -> ⟦ der ⟧ f (a, b) = f' ->
  (forall x, x ∈ (a, b) -> f' x < 0) ->
  decreasing_on f [a, b].
Proof.
  intros f f' a b H1 H2 H3 H4 x1 x2 H5 H6 H7.
  assert (H8 : differentiable_on f (x1, x2)).
  {
    intros x H8. left. split. apply is_interior_point_open; solve_R.
    specialize (H3 x ltac:(solve_R)) as [[_ H3] | [[H3 _] | [H3 _]]].
    - exists (f' x). auto.
    - apply left_interval_endpoint_open in H3; solve_R.
    - apply right_interval_endpoint_open in H3; solve_R.
  }

  assert (H9 : continuous_on f [x1, x2]).
  { apply continuous_on_subset with (A2 := [a, b]); auto. intros x H9. solve_R. }

  pose proof (theorem_11_4 f x1 x2 H7 H9 H8) as [c [H10 H11]].
  
  specialize (H3 c).
  set (h := fun _ : R => (f x2 - f x1) / (x2 - x1)). assert (h c = f' c) as H12.
  {
    apply derivative_of_function_at_x_unique with (f := f); auto. specialize (H3 ltac:(solve_R)) as [[_ H3] | [[H3 _] | [H3 _]]].
    - apply H3.
    - apply left_interval_endpoint_open in H3; solve_R.
    - apply right_interval_endpoint_open in H3; solve_R.
  }
  specialize (H4 c ltac:(solve_R)). unfold h in H12.
  assert (H13 : (f x2 - f x1) / (x2 - x1) < 0) by lra.
  apply Rmult_lt_compat_r with (r := (x2 - x1)) in H13; field_simplify in H13; lra.
Qed.

Theorem theorem_11_8 : forall f f' g g' a b,
  a < b -> continuous_on f [a, b] -> continuous_on g [a, b] -> ⟦ der ⟧ f (a, b) = f' -> ⟦ der ⟧ g (a, b) = g' ->
    exists x, x ∈ (a, b) /\ (f b - f a) * g' x = (g b - g a) * f' x.
Proof.
  intros f f' g g' a b H1 H2 H3 H4 H5. set (h := λ x, (g b - g a) * f x - (f b - f a) * g x).
  assert (continuous_on h [a, b]) as H6.
  {
    intros x H6. specialize (H2 x H6). specialize (H3 x H6). unfold h.
    apply limit_on_minus; apply limit_on_mult; auto; apply limit_on_minus; apply limit_on_const.
  }
  assert (differentiable_on h (a, b)) as H7.
  {
    intros x H7. left. split. apply is_interior_point_open; solve_R. specialize (H4 x H7). specialize (H5 x H7). unfold derivative_at in H4, H5.
    assert (H8 : ⟦ lim 0 ⟧ (λ h : ℝ, (f (x + h) - f x) / h) = f' x).
    {
      destruct H4 as [[_ H4] | [[H4 _] | [H4 _]]]; auto.
      - exfalso. apply (left_interval_endpoint_open a b x H1); auto.
      - exfalso. apply (right_interval_endpoint_open a b x H1); auto.
    }
    assert (H9 : ⟦ lim 0 ⟧ (λ h : ℝ, (g (x + h) - g x) / h) = g' x).
    {
       destruct H5 as [[_ H5] | [[H5 _] | [H5 _]]]; auto.
      - exfalso. apply (left_interval_endpoint_open a b x H1); auto.
      - exfalso. apply (right_interval_endpoint_open a b x H1); auto.
    }
    clear H4 H5. rename H8 into H4, H9 into H5.
    unfold h, differentiable_at. exists ((g b - g a) * f' x - (f b - f a) * g' x).
    apply limit_to_0_equiv with (f1 := (λ h, ((g b - g a) * ((f (x + h) - f x)/h)) - ((f b - f a) * ((g (x + h) - g x)/h)))).
    - intros h0 H8. solve_R.
    - apply limit_minus; apply limit_mult; solve_lim.
  }
  assert (h a = f a * g b - g a * f b) as H8. { unfold h. lra. }
  assert (h b = f a * g b - g a * f b) as H9. { unfold h. lra. }
  assert (h a = h b) as H10 by lra. pose proof theorem_11_3 h a b H1 H6 H7 H10 as [x [H11 H12]].
  assert (⟦ der x ⟧ h = (λ x, (g b - g a) * f' x - (f b - f a) * g' x)) as H13.
  { apply theorem_10_3_c; apply theorem_10_5; auto; try (apply derivative_on_imp_derivative_at with (a := a) (b := b); auto). }
  exists x; split; auto. set (h1' := (λ x, (g b - g a) * f' x - (f b - f a) * g' x)). set (h2' := (λ _ : R, 0)).
  assert (h1' x = h2' x) as H14. { apply derivative_of_function_at_x_unique with (f := h); auto. }
  unfold h1', h2' in H14. lra.
Qed.

Theorem cauchy_mvt : forall f f' g g' a b,
  a < b -> continuous_on f [a, b] -> continuous_on g [a, b] -> ⟦ der ⟧ f (a, b) = f' -> ⟦ der ⟧ g (a, b) = g' -> 
    (forall x, x ∈ (a, b) -> g' x <> 0) -> g b <> g a -> exists x, x ∈ (a, b) /\ (f b - f a) / (g b - g a) = f' x / g' x.
Proof.
  intros f f' g g' a b H1 H2 H3 H4 H5 H6 H7. pose proof theorem_11_8 f f' g g' a b H1 H2 H3 H4 H5 as [x [H8 H9]].
  exists x; split; auto. solve_R; split; solve_R.
Qed.

Lemma deriv_test : der (λ x : ℝ, x^2) = (λ x : ℝ, 2 * x).
Proof.
  intros x. replace ((λ x : ℝ, 2 * x)) with ((λ x : ℝ, 2 * x^(2-1))).
  2 : { extensionality y. simpl. lra. } apply power_rule'; auto.
Qed.

Theorem theorem_11_9 : forall f f' g g' a L,
  ⟦ lim a ⟧ f = 0 -> ⟦ lim a ⟧ g = 0 ->
  ⟦ der a ⟧ f = f' -> ⟦ der a ⟧ g = g' ->
  (exists δ, δ > 0 /\ forall x, x ∈ (a - δ, a + δ) -> x <> a -> ⟦ der x ⟧ f = f') ->
  (exists δ, δ > 0 /\ forall x, x ∈ (a - δ, a + δ) -> x <> a -> ⟦ der x ⟧ g = g') ->
  (exists δ, δ > 0 /\ forall x, x ∈ (a - δ, a + δ) -> x <> a -> g' x <> 0) ->
  ⟦ lim a ⟧ (f' / g') = L ->
  ⟦ lim a ⟧ (f / g) = L.
Proof.
  intros f f' g g' a L H1 H2 H3 H4 [δ1 [H5 H6]] [δ2 [H7 H8]] [δ3 [H9 H10]] H11.
  assert (H12 : f a = 0).
  { apply limit_of_function_unique with (f := f) (a := a); auto. apply theorem_9_1_a. exists (f' a); apply H3. }
  assert (H13 : g a = 0).
  { apply limit_of_function_unique with (f := g) (a := a); auto. apply theorem_9_1_a. exists (g' a); apply H4. }
  intros ε H14. specialize (H11 ε H14) as [δ4 [H15 H16]].
  set (δ := Rmin (Rmin δ1 (Rmin δ2 δ3)) δ4). exists δ; split; [solve_R|].
  intros x H17. assert (a < x \/ x < a) as [H18 | H18] by solve_R.
  - assert (H19 : continuous_on f [a, x]).
    { 
      intros y H19. destruct (Req_dec_T y a) as [H20 | H20].
      - subst y. apply limit_imp_limit_on. apply theorem_9_1_a. exists (f' a). apply H3.
      - apply limit_imp_limit_on. apply theorem_9_1_a. exists (f' y). apply H6; unfold δ in *; solve_R. 
    }
    assert (H20 : continuous_on g [a, x]).
    {
      intros y H20. destruct (Req_dec_T y a) as [H21 | H21].
      - subst y. apply limit_imp_limit_on. apply theorem_9_1_a. exists (g' a). apply H4.
      - apply limit_imp_limit_on. apply theorem_9_1_a. exists (g' y). apply H8; unfold δ in *; solve_R. 
    }
    assert (H21 : ⟦ der ⟧ f (a, x) = f').
    { intros y H21. left. split. apply is_interior_point_open; solve_R. apply H6; unfold δ in *; solve_R. }
    assert (H22 : ⟦ der ⟧ g (a, x) = g').
    { intros y H22. left. split. apply is_interior_point_open; solve_R. apply H8; unfold δ in *; solve_R. }
    assert (H23 : forall y, y ∈ (a, x) -> g' y <> 0).
    { intros y H23. apply H10; unfold δ in *; solve_R. }
    assert (H24 : g x <> g a).
    {
      intro H24. pose proof (theorem_11_3 g a x H18 H20) as [c [H25 H26]]; auto.
      - apply derivative_on_imp_differentiable_on with (f' := g'); auto.
      - specialize (H23 c H25). specialize (H22 c H25) as [[ _ H22 ] | [ [ H22 _ ] | [ H22 _ ] ] ].
        -- pose proof derivative_of_function_at_x_unique g g' (fun _ => 0) c H22 H26 as H27; auto.
        -- apply left_interval_endpoint_open in H22; solve_R.
        -- apply right_interval_endpoint_open in H22; solve_R.
    }
    pose proof cauchy_mvt f f' g g' a x H18 H19 H20 H21 H22 H23 H24 as [c [H25 H26]].
    rewrite H12, H13 in H26. rewrite Rminus_0_r, Rminus_0_r in H26.
    specialize (H16 c ltac:(unfold δ in *; solve_R)). solve_R.
  - assert (H19 : continuous_on f [x, a]).
    { 
      intros y H19. destruct (Req_dec_T y a) as [H20 | H20].
      - subst y. apply limit_imp_limit_on. apply theorem_9_1_a. exists (f' a). apply H3.
      - apply limit_imp_limit_on. apply theorem_9_1_a. exists (f' y). apply H6; unfold δ in *; solve_R. 
    }
    assert (H20 : continuous_on g [x, a]).
    {
      intros y H20. destruct (Req_dec_T y a) as [H21 | H21].
      - subst y. apply limit_imp_limit_on. apply theorem_9_1_a. exists (g' a). apply H4.
      - apply limit_imp_limit_on. apply theorem_9_1_a. exists (g' y). apply H8; unfold δ in *; solve_R. 
    }
    assert (H21 : ⟦ der ⟧ f (x, a) = f').
    { intros y H21. left. split. apply is_interior_point_open; solve_R. apply H6; unfold δ in *; solve_R. }
    assert (H22 : ⟦ der ⟧ g (x, a) = g').
    { intros y H22. left. split. apply is_interior_point_open; solve_R. apply H8; unfold δ in *; solve_R. }
    assert (H23 : forall y, y ∈ (x, a) -> g' y <> 0).
    { intros y H23. apply H10; unfold δ in *; solve_R. }
    assert (H24 : g a <> g x).
    {
      intro H24. pose proof (theorem_11_3 g x a H18 H20) as [c [H25 H26]]; auto.
      - apply derivative_on_imp_differentiable_on with (f' := g'); auto.
      - specialize (H23 c H25). specialize (H22 c H25) as [[ _ H22 ] | [ [ H22 _ ] | [ H22 _ ] ] ].
        -- pose proof derivative_of_function_at_x_unique g g' (fun _ => 0) c H22 H26 as H27; auto.
        -- apply left_interval_endpoint_open in H22; solve_R.
        -- apply right_interval_endpoint_open in H22; solve_R.
    }
    pose proof cauchy_mvt f f' g g' x a H18 H19 H20 H21 H22 H23 H24 as [c [H25 H26]].
    rewrite H12, H13 in H26. rewrite Rminus_0_l, Rminus_0_l, Rdiv_neg_neg_eq in H26.
    specialize (H16 c ltac:(unfold δ in *; solve_R)). solve_R.
Qed.

Theorem lhopitals_rule : forall f g f' g' a,
  ⟦ lim a ⟧ f = 0 ->
  ⟦ lim a ⟧ g = 0 ->
  ⟦ der a ⟧ f = f' ->
  ⟦ der a ⟧ g = g' ->
  g' a <> 0 ->
  ⟦ lim a ⟧ (f / g) = (f' a / g' a).
Proof.
  intros f g f' g' a H1 H2 H3 H4 H5.
  assert (H6 : f a = 0).
  { apply limit_of_function_unique with (f := f) (a := a); auto. apply theorem_9_1_a. exists (f' a). apply H3. }
  assert (H7 : g a = 0).
  { apply limit_of_function_unique with (f := g) (a := a); auto. apply theorem_9_1_a. exists (g' a). apply H4. }
  assert (H8 : ⟦ lim a ⟧ (λ x : ℝ, (g x - g a) / (x - a)) = g' a).
  { 
    replace a with (0 + a) at 1 by lra. rewrite <- limit_shift with (a := 0) (c := a).
    apply limit_to_a_equiv with (f1 := fun h => (g (a + h) - g a) / h); auto.
    intros h H9. replace (h + a - a) with h by lra. rewrite Rplus_comm. reflexivity.
  }
  assert (H9 : ⟦ lim a ⟧ (λ x : ℝ, (f x - f a) / (x - a)) = f' a).
  { 
    replace a with (0 + a) at 1 by lra. rewrite <- limit_shift with (a := 0) (c := a).
    apply limit_to_a_equiv with (f1 := fun h => (f (a + h) - f a) / h); auto.
    intros h H9. replace (h + a - a) with h by lra. rewrite Rplus_comm. reflexivity.
  }
  pose proof limit_neq_x_exists_neighborhood (fun x => (g x - g a) / (x - a)) a (g' a) 0 H8 H5 as [δ [H10 H11]].
  apply limit_to_a_equiv' with (f1 := fun x => ((f x - f a) / (x - a)) / ((g x - g a) / (x - a))) (δ := δ); auto.
  - intros x [H12 H13]. specialize (H11 x ltac:(solve_R)). solve_R.
  - apply limit_div; auto.
Qed.
  
Lemma derivative_on_all_imp_derivative : forall f f',
  (forall a b, a < b -> ⟦ der ⟧ f [a, b] = f') -> ⟦ der ⟧ f = f'.
Proof.
  intros f f' H1 x ε H2. specialize (H1 (x - ε) (x + ε) ltac:(solve_R)) as H3.
  specialize (H3 x ltac:(solve_R)) as [[H4  H5] | [[H4 _] | [H4 _]]].
  - specialize (H5 ε H2); auto.
  - exfalso. apply (not_left_endpoint (x - ε) (x + ε) x); solve_R.
  - exfalso. apply (not_right_endpoint (x - ε) (x + ε) x); solve_R.
Qed.

Lemma derivative_on_sub_interval : forall f f' a b c d,
  a <= c < d <= b -> ⟦ der ⟧ f [a, b] = f' -> ⟦ der ⟧ f [c, d] = f'.
Proof.
  intros f f' a b c d H1 H2 x H3.
  assert (H4 : x ∈ [a, b]) by solve_R.
  specialize (H2 x H4) as [[H6 H7] | [[H6 H7] | [H6 H7]]].
  - assert (x = c \/ x = d \/ (c < x < d)) as [H8 | [H8 | H8]] by solve_R.
    -- subst x. right; left; split.
      --- apply left_interval_enpoint_closed; lra.
      --- apply derivative_at_iff in H7; tauto.
    -- subst x. right; right; split.
      --- apply right_interval_enpoint_closed; lra.
      --- apply derivative_at_iff in H7; tauto.
    -- left; split.
      --- apply is_interior_point_closed; solve_R.
      --- assumption.
  - assert (H8: x = c) by (apply is_left_endpoint_closed in H6; solve_R).
    subst x. right; left; split.
    -- apply left_interval_enpoint_closed; lra.
    -- assumption.
  - assert (H8: x = d) by (apply is_right_endpoint_closed in H6; solve_R).
    subst x; right; right; split.
    -- apply right_interval_enpoint_closed; lra.
    -- assumption.
Qed.

Lemma derivative_on_closed_eq : forall a b f1 f2 f',
  a < b -> (forall x, a <= x <= b -> f1 x = f2 x) -> ⟦ der ⟧ f1 [a, b] = f' -> ⟦ der ⟧ f2 [a, b] = f'.
Proof.
  intros a b f1 f2 f' H1 H2 H3 c H4. specialize (H3 c H4) as [[H3 H5] | [[H3 H5] | [H3 H5]]].
  - left; split; auto. intros ε H6. specialize (H5 ε H6) as [δ [H7 H8]].
    apply is_interior_point_closed in H3; auto.
    exists (Rmin δ (Rmin (b - c) (c - a))). split. solve_R.
    intros x H9. specialize (H8 x ltac:(solve_R)). repeat rewrite <- H2; solve_R.
  - right; left; split; auto. apply is_left_endpoint_closed in H3; auto.
    intros ε H6. specialize (H5 ε H6) as [δ [H7 H8]]. 
    exists (Rmin δ (b - c)). split. solve_R.
    intros x H9. specialize (H8 x ltac:(solve_R)). repeat rewrite <- H2; solve_R.
  - right; right; split; auto. apply is_right_endpoint_closed in H3; auto.
    intros ε H6. specialize (H5 ε H6) as [δ [H7 H8]].
    exists (Rmin δ (c - a)). split. solve_R.
    intros x H9. specialize (H8 x ltac:(solve_R)). repeat rewrite <- H2; solve_R.
Qed.

Lemma derivative_on_closed_eq' : forall a b f f1' f2',
  a < b -> (forall x, a <= x <= b -> f1' x = f2' x) -> ⟦ der ⟧ f [a, b] = f1' -> ⟦ der ⟧ f [a, b] = f2'.
Proof.
  intros a b f f1' f2' H1 H2 H3 c H4. specialize (H3 c H4) as [[H3 H5] | [[H3 H5] | [H3 H5]]].
  - left; split; auto. intros ε H6. specialize (H5 ε H6) as [δ [H7 H8]].
    apply is_interior_point_closed in H3; auto.
    exists (Rmin δ (Rmin (b - c) (c - a))). split. solve_R.
    intros x H9. specialize (H8 x ltac:(solve_R)). repeat rewrite <- H2; solve_R.
  - right; left; split; auto. apply is_left_endpoint_closed in H3; auto.
    intros ε H6. specialize (H5 ε H6) as [δ [H7 H8]]. 
    exists (Rmin δ (b - c)). split. solve_R.
    intros x H9. specialize (H8 x ltac:(solve_R)). repeat rewrite <- H2; solve_R.
  - right; right; split; auto. apply is_right_endpoint_closed in H3; auto.
    intros ε H6. specialize (H5 ε H6) as [δ [H7 H8]].
    exists (Rmin δ (c - a)). split. solve_R.
    intros x H9. specialize (H8 x ltac:(solve_R)). repeat rewrite <- H2; solve_R.
Qed.

Lemma derivative_on_eq : forall f1 f2 f' D,
  (forall x, x ∈ D -> f1 x = f2 x) -> ⟦ der ⟧ f1 D = f' -> ⟦ der ⟧ f2 D = f'.
Proof.
  intros f1 f2 f' D H1 H2 c H3. specialize (H2 c H3) as [[H4 H5] | [[H4 H5] | [H4 H5]]].
  - left. split; auto. destruct H4 as [δD [H6 H7]].
    intros ε H8. specialize (H5 ε H8) as [δ [H9 H10]].
    exists (Rmin δ δD). split. solve_R. intros h H11.
    assert (H12 : (c + h) ∈ D). { apply H7. solve_R. }
    specialize (H1 (c + h) H12) as H13. specialize (H1 c H3).
    rewrite <- H1, <- H13. apply H10. solve_R.
  - right; left. split; auto. destruct H4 as [δD [H6 H7]].
    intros ε H8. specialize (H5 ε H8) as [δ [H9 H10]].
    exists (Rmin δ δD). split. solve_R. intros h H11.
    assert (H12 : (c + h) ∈ D). { apply H7. split; unfold Ensembles.In; solve_R. }
    specialize (H1 (c + h) H12) as H13. specialize (H1 c H3).
    rewrite <- H1, <- H13. apply H10. solve_R.
  - right; right. split; auto. destruct H4 as [δD [H6 H7]].
    intros ε H8. specialize (H5 ε H8) as [δ [H9 H10]].
    exists (Rmin δ δD). split. solve_R. intros h H11.
    assert (H12 : (c + h) ∈ D). { apply H7. split; unfold Ensembles.In; solve_R. }
    specialize (H1 (c + h) H12) as H13. specialize (H1 c H3).
    rewrite <- H1, <- H13. apply H10. solve_R.
Qed.

Lemma derivative_on_eq' : forall f f1' f2' D,
  (forall x, x ∈ D -> f1' x = f2' x) -> ⟦ der ⟧ f D = f1' -> ⟦ der ⟧ f D = f2'.
Proof.
  intros f f1' f2' D H1 H2 c H3. specialize (H2 c H3).
  destruct H2 as [[H4 H5] | [[H4 H5] | [H4 H5]]].
  - left. split; auto.
    unfold derivative_at in *. rewrite <- H1; auto.
  - right; left. split; auto.
    unfold derivative_at_right in *. rewrite <- H1; auto.
  - right; right. split; auto.
    unfold derivative_at_left in *. rewrite <- H1; auto.
Qed.

Lemma derivative_sqrt_x : forall x,
  x > 0 ->
  ⟦ der x ⟧ (λ x, √x) = (λ x, 1 / (2 * √ x)).
Proof.
  intros x H1. unfold derivative_at. apply limit_to_0_equiv' with (f1 := fun h => 1 / (sqrt (x + h) + sqrt x)).
  - exists x; split; auto. intros h H2 H3. assert (√(x+h) > 0) as H4 by (apply sqrt_lt_R0; solve_R).
    assert (√x > 0) as H5 by (apply sqrt_lt_R0; auto).
    apply Rmult_eq_reg_r with (r := √(x+h) + √x); try lra. field_simplify; try lra.
    repeat rewrite pow2_sqrt; solve_R.
  - replace (1 / (2 * √x)) with (1 / (√x + √x)).
    2 : { pose proof sqrt_lt_R0 x H1 as H2. solve_R. }
    apply limit_div. apply limit_const. apply limit_plus.
    2 : { apply limit_const. } pose proof sqrt_f_continuous (fun h => x + h) as H2.
    assert (H3 : continuous (λ h : ℝ, x + h)). { intros a. unfold continuous_at. solve_lim. }
    specialize (H2 H3). specialize (H2 0). unfold continuous_at in H2.
    rewrite Rplus_0_r in H2. apply H2. pose proof sqrt_lt_R0 x H1 as H4. lra.
Qed.

Lemma derivative_sqrt_x_on : forall a b,
  0 < a < b ->
  ⟦ der ⟧ (λ x, √x) [a, b] = (λ x, 1 / (2 * √ x)). 
Proof.
  intros a b H1 x H2. assert (x = a \/ x = b \/ (a < x < b)) as [H3 | [H3 | H3]] by solve_R.
  - subst x. right; left; split. apply left_interval_enpoint_closed; lra.
    apply derivative_at_iff. apply derivative_sqrt_x; lra.
  - subst x. right; right; split. apply right_interval_enpoint_closed; lra.
    apply derivative_at_iff. apply derivative_sqrt_x; lra.
  - left; split. apply is_interior_point_closed; solve_R.
    apply derivative_sqrt_x; lra.
Qed.

Lemma derivative_sqrt_f : forall f f' x,
  f x > 0 ->
  ⟦ der x ⟧ f = f' ->
  ⟦ der x ⟧ (λ x, √(f x)) = (λ x, (f' x) / (2 * √(f x))).
Proof.
  intros f f' x H1 H2. set (g := sqrt). set (g' := λ x, 1 / (2 * √ x)).
  assert (H3 : forall x, x > 0 -> ⟦ der x ⟧ g = g'). { unfold g, g'. intros y H3. apply derivative_sqrt_x; auto. }
  replace (λ x0 : ℝ, f' x0 / (2 * g (f x0))) with (g' ∘ f ∙ f').
  2 : { extensionality y. unfold g, g', compose. lra. }
  assert (H4 : ⟦ der f x ⟧ g = g'). { apply H3. apply H1. }
  apply (theorem_10_9 g f g' f' x H2 H4).
Qed.

Lemma nth_derivative_test : ⟦ der ^ 2 ⟧ (λ x : ℝ, x^3) = (λ x : ℝ, 6 * x).
Proof.
  exists (λ x : ℝ, 3 * x^2). split.
  - apply power_rule'; solve_R.
  - exists (λ x : ℝ, 6 * x). split.
    -- replace (λ x : ℝ, 6 * x) with (λ x : ℝ, 3 * (2 * x^(2-1))).
       2 : { extensionality y. simpl. lra. }
       apply theorem_10_5'. apply power_rule'; solve_R. 
    -- simpl. reflexivity.
Qed.

Lemma Derive_eq : forall f f',
  ⟦ der ⟧ f = f' -> ⟦ Der ⟧ f = f'.
Proof.
  intros f f' H1.
  unfold Derive.
  assert (H2: is_derive_or_zero f (epsilon (inhabits (fun _ => 0)) (is_derive_or_zero f))).
  { apply epsilon_spec. exists f'. left. auto. }
  
  unfold is_derive_or_zero in H2.
  destruct H2 as [H2 | [H2 _]].
  - apply derivative_of_function_unique with (f := f); auto.
  - exfalso. apply H2. exists f'. auto.
Qed.

Lemma Derive_on_eq : forall f f' D x,
  x ∈ D -> 
  ⟦ der ⟧ f D = f' -> 
  (⟦ Der ⟧ f D) x = f' x.
Proof.
  intros f f' D x H1 H2.
  unfold Derive_on.
  assert (H3: exists g, is_derive_on_or_zero f D g).
  { exists f'. left. auto. }
  
  pose proof (epsilon_spec (inhabits (fun _ => 0)) (is_derive_on_or_zero f D) H3) as H4.
  destruct H4 as [H4 | [H4 _]].
  - apply (derivative_of_function_on_unique f (epsilon (inhabits (fun _ => 0)) (is_derive_on_or_zero f D)) f' D); auto.
  - exfalso. apply H4. exists f'. auto.
Qed.

Lemma Derive_spec : forall f f',
  differentiable f ->
  (⟦ der ⟧ f = f' <-> ⟦ Der ⟧ f = f').
Proof.
  intros f f' H1.
  split.
  - intros H2. apply Derive_eq. assumption.
  - intros H2. subst f'. unfold Derive.
    assert (H3: is_derive_or_zero f (epsilon (inhabits (fun _ => 0)) (is_derive_or_zero f))).
    { 
      apply epsilon_spec. pose proof differentiable_imp_exists_derivative f H1 as [f' H3].
      exists f'. left. assumption.
    }
    destruct H3 as [H3 | [H3 _]]; auto.
    exfalso. apply H3. apply differentiable_imp_exists_derivative; auto.
Qed.

Lemma differentiable_plus : forall f g,
  differentiable f -> differentiable g -> differentiable (λ x, f x + g x).
Proof.
  intros f g H1 H2 x. unfold differentiable_at in *.
  specialize (H1 x) as [L1 H3]. specialize (H2 x) as [L2 H4].
  exists (L1 + L2).
  intros ε H5. specialize (H3 (ε / 2)) as [δ1 [H6 H7]]; [solve_R |].
  specialize (H4 (ε / 2)) as [δ2 [H8 H9]]; [solve_R |].
  exists (Rmin δ1 δ2). split. solve_R. intros h H10.
  specialize (H7 h ltac:(solve_R)). specialize (H9 h ltac:(solve_R)).
  solve_R.
Qed.

Lemma differentiable_sum : forall (i n : nat) (f : nat -> R -> R),
  (i <= n)%nat -> (forall k, differentiable (f k)) -> differentiable (λ x, ∑ i n (λ k, f k x)).
Proof.
  intros i n f H1. induction n as [| k IH].
  - replace (λ x0 : ℝ, ∑ i 0 λ k : ℕ, f k x0) with (λ x0 : ℝ, f 0%nat x0); auto. extensionality x. destruct i. reflexivity. 
    rewrite sum_f_Sn_n; try lia. 
  - assert (i = S k \/ i <= k)%nat as [H2 | H2] by lia.
    -- subst i. replace (λ x0 : ℝ, ∑ (S k) (S k) (λ k0 : ℕ, f k0 x0)) with (λ x0 : ℝ, f (S k) x0); auto.
       extensionality x. rewrite sum_f_n_n; auto.
    -- intros H3. replace (λ x0 : ℝ, ∑ i (S k) (λ k0 : ℕ, f k0 x0)) with (λ x0 : ℝ, (∑ i k (λ k0 : ℕ, f k0 x0)) + f (S k) x0).
       2 : { extensionality y. rewrite sum_f_i_Sn_f; try lia. reflexivity. }
       apply differentiable_plus; auto.
Qed.

Lemma Derive_plus : forall f g,
  differentiable f -> differentiable g ->
  ⟦ Der ⟧ (λ x, f x + g x) = (λ x, (⟦ Der ⟧ f) x + (⟦ Der ⟧ g) x).
Proof.
  intros f g H1 H2. pose proof differentiable_plus f g H1 H2 as H3.
  pose proof Derive_spec f (⟦ Der ⟧ f) H1 as H4.
  pose proof Derive_spec g (⟦ Der ⟧ g) H2 as H5.
  pose proof Derive_spec (λ x, f x + g x) (λ x, (⟦ Der ⟧ f) x + (⟦ Der ⟧ g) x) H3 as H6.
  apply H6. apply theorem_10_3_b. apply H4. reflexivity. apply H5. reflexivity.
Qed.

Lemma nth_Derive_S : forall n f,
  nth_Derive (S n) f = nth_Derive n (Derive f).
Proof.
  induction n as [| k IH].
  - reflexivity.
  - intros f. simpl. rewrite <- IH. reflexivity.
Qed.

Lemma nth_Derive_on_S : forall n f D,
  ⟦ Der^(S n) ⟧ f D = ⟦ Der^n ⟧ (⟦ Der ⟧ f D) D.
Proof.
  induction n as [| k IH].
  - reflexivity.
  - intros f D. simpl. rewrite <- IH. reflexivity.
Qed.

Lemma nth_Derive_eq : forall n f f',
  ⟦ der ^ n ⟧ f = f' -> ⟦ Der ^ n ⟧ f = f'.
Proof.
  induction n as [| k IH]; intros f f' H1; simpl in H1.
  - subst. reflexivity.
  - destruct H1 as [f1' [H1 H2]].
    rewrite nth_Derive_S.
    apply Derive_eq in H1.
    rewrite H1.
    apply IH.
    auto.
Qed.

Lemma nth_derivative_at_1_iff : forall f f' a,
  ⟦ der ^ 1 a ⟧ f = f' a <-> ⟦ der a ⟧ f = f'.

Lemma nth_Derive_at_eq : forall n a f fn',
  ⟦ der ^ n a ⟧ f = fn' a -> ⟦ Der ^ n a ⟧ f = fn' a.
Proof.
  intros n a f fn' H1. induction n as [| k IH].
  - simpl in *. auto.
  - destruct H1 as [δ [fk' [H3 [H4 H5]]]].
    rewrite nth_Derive_S.
    apply Derive_eq in H3; auto.

Qed.

Lemma nth_Derive_at_eq' : forall n a f f',
  ⟦ der ^ n a ⟧ f = f' -> ⟦ Der ^ n a ⟧ f = f'.
Proof.
  intros n a f f' [fn' [H1 H2]].
  pose proof nth_Derive_eq n f fn' H1 as H3.
  unfold nth_Derive_at.
  rewrite H3.
  auto.
Qed.

Lemma nth_differentiable_imp_differentiable : forall f n,
 (n > 0)%nat -> nth_differentiable n f -> differentiable f.
Proof.
  intros f n H1 [f' H2].
  destruct n; try lia. destruct H2 as [f'' [H3 H4]].
  apply derivative_imp_differentiable with (f' := f''); auto.
Qed.

Lemma nth_differentiable_imp_differentiable_at : forall f n a,
 (n > 0)%nat -> nth_differentiable n f -> differentiable_at f a.
Proof.
  intros f n a H1 H2.
  apply nth_differentiable_imp_differentiable in H2; try lia.
  unfold differentiable_at. specialize (H2 a). tauto.
Qed.

Lemma Derive_nth_Derive : forall n f,
  ⟦ Der ⟧ (⟦ Der ^ n ⟧ f) = ⟦ Der ^ (S n) ⟧ f.
Proof.
  reflexivity.
Qed.

Lemma Derive_nth_Derive_on : forall n f D,
  ⟦ Der ⟧ (⟦ Der ^ n ⟧ f D) D = ⟦ Der ^ (S n) ⟧ f D.
Proof.
  intros n f D. simpl. reflexivity.
Qed.

Lemma nth_derivative_nth_Derive : forall n f,
  nth_differentiable n f ->
  (⟦ der ^ n ⟧ f = ⟦ Der ^ n⟧ f).
Proof.
  intros n.
  induction n as [| k IH].
  -
    intros f H1.
    simpl.
    reflexivity.
  -
    intros f H1.
    simpl.
    exists (Derive f).
    split.
    + apply nth_differentiable_imp_differentiable in H1; try lia.  pose proof Derive_spec f (Derive f) H1 as H2; tauto.
    + rewrite Derive_nth_Derive. rewrite nth_Derive_S.
      apply IH. destruct H1 as [f'' [f' [H1 H2]]]. exists f''.
      apply Derive_eq in H1. rewrite H1; auto.
Qed.

Lemma nth_Derive_mth_Derive : forall n m f,
  ⟦ Der ^ n ⟧ (⟦ Der ^ m ⟧ f) = ⟦ Der ^ (n + m) ⟧ f.
Proof.
  intros n m f. induction n as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma Derive_sum : forall (i n : nat) (f : nat -> R -> R),
  (i <= n)%nat -> (forall k, differentiable (f k)) ->
  ⟦ Der ⟧ (λ x, ∑ i n (λ k, f k x)) = (λ x, ∑ i n (λ k, (⟦ Der ⟧ (f k)) x)).
Proof.
  intros i n f H1 H2. induction n as [| k IH]; extensionality x.
  - replace (λ x0 : ℝ, ∑ 0 0 λ k : ℕ, f k x0) with (λ x0 : ℝ, f 0%nat x0); reflexivity.
  - replace (λ x0 : ℝ, ∑ 0 (S k) λ k0 : ℕ, f k0 x0) with (λ x0 : ℝ, (∑ 0 k λ k0 : ℕ, f k0 x0) + f (S k) x0).
    2 : { extensionality y. rewrite sum_f_i_Sn_f; try lia. reflexivity. }
    assert (i = S k \/ i <= k)%nat as [H3 | H3] by lia.
    -- subst i.
       replace (λ x0 : ℝ, ∑ (S k) (S k) λ k0 : ℕ, f k0 x0) with (λ x0 : ℝ, f (S k) x0); auto.
       rewrite sum_f_n_n. reflexivity. extensionality y. rewrite sum_f_n_n; auto.
    -- replace (λ x0 : ℝ, ∑ i (S k) λ k0 : ℕ, f k0 x0) with (λ x0 : ℝ, (∑ i k λ k0 : ℕ, f k0 x0) + f (S k) x0).
       2 : { extensionality y. rewrite sum_f_i_Sn_f; try lia. reflexivity. }
       rewrite Derive_plus; auto.
       rewrite IH; try lia. 2 : { apply differentiable_sum; auto. }
       rewrite sum_f_i_Sn_f; try lia. reflexivity.
Qed.

Lemma nth_derivative_mult_const_l : forall n f f' c,
  ⟦ der ^ n ⟧ f = f' -> ⟦ der ^ n ⟧ (c * f) = (c * f').
Proof.
  induction n as [| k IH]; intros f f' c H1.
  - simpl in *. subst. reflexivity.
  - simpl in *. destruct H1 as [g [H1 H2]].
    exists (c * g)%f. split.
    -- apply theorem_10_5'; auto.
    -- apply IH; auto.
Qed.

Lemma nth_derivative_mult_const_r : forall n f f' c,
  ⟦ der ^ n ⟧ f = f' -> ⟦ der ^ n ⟧ (fun x => f x * c) = (fun x => f' x * c).
Proof.
  intros n f f' c H1. replace (fun x => f x * c) with (fun x => c * f x).
  2 : { extensionality y. lra. } 
  replace (fun x => f' x * c) with (fun x => c * f' x).
  2 : { extensionality y. lra. } apply nth_derivative_mult_const_l; auto.
Qed.

Lemma nth_derivative_pow : forall k n, (k <= n)%nat ->
  ⟦ der ^ k ⟧ (fun x => x ^ n) = (fun x => (n! / (n-k)!) * x ^ (n - k)).
Proof.
  induction k as [| k IH].
  - intros n H1. simpl. extensionality x. rewrite Nat.sub_0_r. field. apply INR_fact_neq_0.
  - intros n H1. destruct n as [| n']; try lia. simpl.
    specialize (IH n' ltac:(lia)). exists (λ x, INR (S n') * x ^ n'). split.
    -- replace (λ x : ℝ, x * x ^ n') with (λ x : ℝ, x ^ (S n')).
       2 : { extensionality y. simpl. lra. } replace (λ x, S n' * x ^ n') with (λ x, S n' * x ^ (S n' - 1)).
       2 : { extensionality y. replace (S n' - 1)%nat with n' by lia. reflexivity. }
       apply power_rule'; reflexivity.
    -- replace (λ x : ℝ, (n'! + n' * n'!)%nat / (n' - k)! * x ^ (n' - k)) with (λ x : ℝ, (S n') * (n'! / (n' - k)! * x ^ (n' - k))).
       2 : { extensionality y. replace (n'! + n' * n'!)%nat with (S n' * n'!)%nat by lia. rewrite mult_INR. lra. }
       apply nth_derivative_mult_const_l; auto.
Qed.

Lemma nth_derivative_const : forall n c,
  (n > 0)%nat -> ⟦ der ^ n ⟧ (λ _, c) = (λ x, 0).
Proof.
  intros n c. generalize dependent c. induction n as [| k IH]; try lia.
  - intros c H1. assert ((k = 0)%nat \/ (k > 0)%nat) as [H2 | H2] by lia.
    -- subst k. exists (λ x, 0). split.
       ++ apply theorem_10_1.
       ++ reflexivity.
    -- specialize (IH c H2) as H3. exists (λ x, 0). split.
       ++ apply theorem_10_1.
       ++ apply IH; auto.
Qed. 

Lemma nth_derivative_pow_gt : forall k n, (k > n)%nat ->
  ⟦ der ^ k ⟧ (fun x => x ^ n) = (fun x => 0).
Proof.
  induction k as [| k IH]; intros n H1; try lia.
  simpl. destruct n as [| n'].
  - exists (fun x => 0). split.
    -- replace (λ _ : ℝ, 0) with (λ x, 0 * (x ^ (0 -1))) by (extensionality y; simpl; lra).
       apply power_rule.
    -- destruct k; try reflexivity. apply nth_derivative_const; lia.
  - specialize (IH n' ltac:(lia)). exists (fun x => INR (S n') * x ^ (S n' - 1)). split.
    -- apply power_rule'; reflexivity.
    -- replace (S n' - 1)%nat with n' by lia. replace (λ _ : ℝ, 0) with (λ x : ℝ, S n' * 0).
       2 : { extensionality x. lra. } apply nth_derivative_mult_const_l; auto.
Qed.

Lemma nth_derivative_x_i_at_0 : ∀ i k,
  ⟦ der^k 0 ⟧ (fun x => x ^ i) = (if Nat.eq_dec i k then INR (fact k) else 0).
Proof.
  intros i k. destruct (Nat.eq_dec i k) as [H1 | H1].
  - subst i. exists (fun x => (INR (fact k) / INR (fact (k - k))) * x ^ (k - k)). split.
    -- apply nth_derivative_pow; lia.
    -- rewrite Nat.sub_diag. simpl. lra.
  - destruct (le_gt_dec k i) as [H2 | H2].
    -- exists (fun x => (INR (fact i) / INR (fact (i - k))) * x ^ (i - k)). split.
       --- apply nth_derivative_pow; lia.
       --- assert (H3 : (i - k > 0)%nat) by lia. destruct (i - k)%nat; try lia. simpl. lra.
    -- exists (fun x => 0). split; try reflexivity. apply nth_derivative_pow_gt; lia.
Qed.

Lemma nth_derivative_of_function_at_x_unique : forall n f f1' f2' x,
  ⟦ der ^ n ⟧ f = f1' -> ⟦ der ^ n ⟧ f = f2' -> f1' x = f2' x.
Proof.
  intros n f f1' f2' x H1 H2.
  pose proof (nth_derivative_of_function_unique n f f1' f2' H1 H2).
  subst. reflexivity.
Qed.

Lemma differentiable_mult_const_l : forall f c,
  differentiable f -> differentiable (λ x, c * f x).
Proof.
  intros f c H1. pose proof differentiable_imp_exists_derivative f H1 as [f' H2].
  pose proof theorem_10_5' f f' c H2 as H3.
  apply derivative_imp_differentiable with (f' := (c * f')%f); auto.
Qed.

Lemma differentiable_mult_const_r : forall f c,
  differentiable f -> differentiable (λ x, f x * c).
Proof.
  intros f c H1. replace (λ x, f x * c) with (λ x, c * f x).
  2 : { extensionality y. lra. } apply differentiable_mult_const_l; auto.
Qed.

Lemma differentiable_pow : forall n,
  differentiable (λ x, x ^ n).
Proof.
  intros n. apply derivative_imp_differentiable with (f' := λ x, INR n * x ^ (n - 1)).
  apply power_rule'; reflexivity.
Qed.

Lemma nth_Derive_spec : forall n f f',
  nth_differentiable n f ->
  (⟦ der ^ n ⟧ f = f' <-> ⟦ Der ^ n ⟧ f = f').
Proof.
  intros n f f' H1.
  split.
  - intro H2.
    pose proof (nth_derivative_nth_Derive n f H1) as H3.
    apply nth_derivative_of_function_unique with (n:=n) (f:=f); assumption.
  - intro H2. subst f'. apply nth_derivative_nth_Derive; auto.
Qed.

Lemma nth_Derive_at_spec : forall n a f f',
  nth_differentiable n f ->
  (⟦ der ^ n a ⟧ f = f' <-> ⟦ Der ^ n a ⟧ f = f').
Proof.
  intros n a f f' H1. split; intros H2.
  - apply nth_Derive_at_eq'; auto.
  - exists (nth_Derive n f). split; auto. apply nth_Derive_spec; auto.
Qed.

Lemma nth_differentiable_mult_const_l : forall n f c,
  nth_differentiable n f -> nth_differentiable n (λ x, c * f x).
Proof.
  intros n f c [fn' H].
  exists (c * fn')%f.
  apply nth_derivative_mult_const_l; auto.
Qed.

Lemma nth_differentiable_mult_const_r : forall n f c,
  nth_differentiable n f -> nth_differentiable n (λ x, f x * c).
Proof.
  intros n f c H1. replace (λ x, f x * c) with (λ x, c * f x).
  2 : { extensionality y. lra. } apply nth_differentiable_mult_const_l; auto.
Qed.

Lemma nth_derivative_plus : forall n f1 f1' f2 f2',
  ⟦ der ^ n ⟧ f1 = f1' -> ⟦ der ^ n ⟧ f2 = f2' ->
    ⟦ der ^ n ⟧ (λ x, f1 x + f2 x) = (λ x, f1' x + f2' x).
Proof.
  induction n as [| k IH]; intros f1 f1' f2 f2' H1 H2.
  - simpl in *. subst. extensionality x. lra.
  - simpl in *. destruct H1 as [g1 [H1 H3]]. destruct H2 as [g2 [H2 H4]].
    exists (g1 + g2)%f. split.
    -- apply theorem_10_3_b; try apply differentiable_plus; auto.
    -- apply IH; auto.
Qed.

Lemma nth_differentiable_plus : forall n f g,
  nth_differentiable n f -> nth_differentiable n g -> nth_differentiable n (f + g).
Proof.
  intros n f g [f' H1] [g' H2]. exists (f' + g')%f.
  apply nth_derivative_plus; auto.
Qed.

Lemma nth_differentiable_sum : forall (i m n : nat) (f : nat -> R -> R),
  (i <= m)%nat -> (forall k, nth_differentiable n (f k)) -> nth_differentiable n (λ x, ∑ i m (λ k, f k x)).
Proof.
  intros i m n f H1 H2.
  assert (forall p, (i <= p)%nat -> nth_differentiable n (λ x, ∑ i p (λ k, f k x))) as H3.
  {
    intros p. induction p as [| k IH].
    - intros Hle. assert (i = 0%nat) by lia. subst.
      replace (λ x, ∑ 0 0 (λ k, f k x)) with (f 0%nat).
      + apply H2.
      + extensionality x. rewrite sum_f_0_0. reflexivity.
    - intros Hle.
      destruct (le_lt_dec i k) as [H_le_k | H_gt_k].
      + replace (λ x, ∑ i (S k) (λ k0, f k0 x)) with (λ x, (∑ i k (λ k0, f k0 x)) + f (S k) x).
        * apply nth_differentiable_plus.
          -- apply IH; auto.
          -- apply H2.
        * extensionality x. rewrite sum_f_i_Sn_f; auto.
      + assert (i = S k) by lia. subst.
        replace (λ x, ∑ (S k) (S k) (λ k0, f k0 x)) with (f (S k)).
        * apply H2.
        * extensionality x. rewrite sum_f_n_n. reflexivity.
  }
  apply H3; auto.
Qed.

Lemma nth_differentiable_pow : forall n m,
  nth_differentiable n (λ x, x ^ m).
Proof.
  intros n m. revert m. induction n as [| k IH].
  - intros m. exists (λ x, x ^ m). simpl. reflexivity.
  - intros m.
    specialize (IH (m - 1)%nat) as [f' H1].
    exists (λ x, INR m * f' x).
    simpl.
    exists (λ x, INR m * x ^ (m - 1)).
    split.
    -- apply power_rule.
    -- apply nth_derivative_mult_const_l; auto.
Qed.

Lemma nth_differentiable_Derive : forall n f,
  nth_differentiable (S n) f -> nth_differentiable n (⟦ Der ⟧ f).
Proof.
  intros n f [fn' H1].
  destruct H1 as [f' [H2 H3]].
  exists fn'.
  assert (H4 : differentiable f).
  { apply derivative_imp_differentiable with (f' := f'); auto. }
  rewrite Derive_spec in H2; auto.
  rewrite H2.
  auto.
Qed.

Lemma differentiable_on_imp_exists_derivative_on : forall f D,
  differentiable_on f D ->
  exists f', ⟦ der ⟧ f D = f'.
Proof.
  intros f D H1.
  destruct (choice (λ x y, (x ∈ D -> 
    (interior_point D x /\ ⟦ der x ⟧ f = (λ _, y)) \/
    (left_endpoint D x /\ ⟦ der x ⁺ ⟧ f = (λ _, y)) \/
    (right_endpoint D x /\ ⟦ der x ⁻ ⟧ f = (λ _, y))) /\
    (~ x ∈ D -> y = 0))) as [f' Hf'].
  - intros x. 
    destruct (classic (x ∈ D)) as [Hin | Hout].
    + specialize (H1 x Hin) as [[Hint Hdiff] | [[Hleft Hdiff] | [Hright Hdiff]]].
      * destruct Hdiff as [L HL]. exists L. split; [left; split; auto | tauto].
      * destruct Hdiff as [L HL]. exists L. split; [right; left; split; auto | tauto].
      * destruct Hdiff as [L HL]. exists L. split; [right; right; split; auto | tauto].
    + exists 0. split; [intros; exfalso; auto | auto].
  - exists f'.
    unfold derivative_on.
    intros a Hin.
    specialize (Hf' a).
    destruct Hf' as [H_on_D _].
    specialize (H_on_D Hin).
    destruct H_on_D as [[H1' H2'] | [[H1' H2'] | [H1' H2']]].
    -- left. split; auto. 
    -- right; left. split; auto.
    -- right; right. split; auto.
Qed.

Lemma Derive_on_imp_derivative_on : forall f f' D,
  differentiable_on f D ->
  ⟦ Der ⟧ f D = f' -> 
  ⟦ der ⟧ f D = f'.
Proof.
  intros f f' D H1 H2.
  rewrite <- H2.
  unfold Derive_on.
  assert (H3 : exists g, is_derive_on_or_zero f D g).
  { 
    destruct (differentiable_on_imp_exists_derivative_on f D H1) as [g H3].
    exists g. left. auto.
  }
  pose proof (epsilon_spec (inhabits (fun _ => 0)) (is_derive_on_or_zero f D) H3) as H4.
  destruct H4 as [H4 | [H4 _]]; auto.
  exfalso. apply H4. apply differentiable_on_imp_exists_derivative_on; auto.
Qed.

Lemma nth_derivative_on_eq : forall n f1 f2 f' D,
  (forall x, x ∈ D -> f1 x = f2 x) ->
  nth_derivative_on n f1 f' D ->
  nth_derivative_on n f2 f' D.
Proof.
  induction n as [| k IH]; intros f1 f2 f' D H1 H2.
  - intros x H3. rewrite <- H1; auto.
  - destruct H2 as [f1' [H2 H3]].
    exists f1'. split.
    -- apply derivative_on_eq with (f1 := f1); auto.
    -- apply IH with (f1 := f1'); auto.
Qed.

Lemma nth_differentiable_on_Derive : forall n f D,
  nth_differentiable_on (S n) f D -> 
  nth_differentiable_on n (⟦ Der ⟧ f D) D.
Proof.
  intros n f D [fn' [f' [H1 H2]]].
  exists fn'.
  apply nth_derivative_on_eq with (f1 := f'); auto.
  intros x H3.
  symmetry.
  apply Derive_on_eq; auto.
Qed.

Lemma nth_Derive_nth_differentiable : forall n m f,
  nth_differentiable (n + m) f -> nth_differentiable m (⟦ Der ^ n ⟧ f).
Proof.
  intros n. induction n as [| k IH].
  - intros m f H1. simpl. auto.
  - intros m f H1.
    rewrite nth_Derive_S.
    apply IH.
    apply nth_differentiable_Derive; auto.
Qed.

Lemma nth_Derive_on_nth_differentiable_on : forall n m f D,
  nth_differentiable_on (n + m) f D -> nth_differentiable_on m (⟦ Der ^ n ⟧ f D) D.
Proof.
  intros n. induction n as [| k IH].
  - intros m f D H1. simpl. auto.
  - intros m f D H1.
    rewrite nth_Derive_on_S.
    apply IH.
    apply nth_differentiable_on_Derive; auto.
Qed.

Lemma nth_differentiable_S_imp_nth_differentiable : forall n f,
  (n > 0)%nat -> nth_differentiable (S n) f -> nth_differentiable n f.
Proof.
  intros n f H1 H2.
  assert (H3 : forall m g, nth_differentiable (S m) g -> nth_differentiable m g).
  {
    intros m. induction m as [| k IH]; intros g H3.
    - exists g. simpl. reflexivity.
    - destruct H3 as [gm' H3]. simpl in H3. destruct H3 as [g' [H4 H5]].
      assert (H6 : nth_differentiable (S k) g') by (exists gm'; auto).
      specialize (IH g' H6) as [gk' H7].
      exists gk'. simpl. exists g'. auto.
  }
  apply H3; auto.
Qed.

Lemma nth_differentiable_on_S_imp_nth_differentiable_on : forall n f D,
  (n > 0)%nat -> nth_differentiable_on (S n) f D -> nth_differentiable_on n f D.
Proof.
  intros n f D H1 H2.
  assert (H3 : forall m g, nth_differentiable_on (S m) g D -> nth_differentiable_on m g D).
  {
    intros m. induction m as [| k IH]; intros g H3.
    - exists g. simpl. intros x Hx. reflexivity.
    - destruct H3 as [gm' H3]. simpl in H3. destruct H3 as [g' [H4 H5]].
      assert (H6 : nth_differentiable_on (S k) g' D). { exists gm'. auto. }
      specialize (IH g' H6).
      destruct IH as [gk' H7].
      exists gk'. simpl. exists g'. split; auto.
  }
  apply H3; auto.
Qed.

Lemma nth_differentiable_le : forall n m f,
  (n <= m)%nat -> nth_differentiable m f -> nth_differentiable n f.
Proof.
  intros n m f H1 H2. generalize dependent n.
  induction m as [| k IH].
  - intros n H1. destruct n; try lia. auto.
  - intros n H1. assert (n = S k \/ n <= k)%nat as [H3 | H3] by lia.
    -- subst n. auto.
    -- apply IH; auto. destruct k. exists f. simpl. reflexivity.
       apply nth_differentiable_S_imp_nth_differentiable; try lia; auto.
Qed.

Lemma nth_differentiable_on_le : forall n m f D,
  (n <= m)%nat -> nth_differentiable_on m f D -> nth_differentiable_on n f D.
Proof.
  intros n m f D H1 H2. generalize dependent n.
  induction m as [| k IH].
  - intros n H1. destruct n; try lia.
    exists f. simpl. auto.
  - intros n H1. assert (n = S k \/ n <= k)%nat as [H3 | H3] by lia.
    -- subst n. auto.
    -- apply IH; auto. destruct k.
       + exists f. simpl. auto.
       + apply nth_differentiable_on_S_imp_nth_differentiable_on; try lia; auto.
Qed.
    
Lemma nth_Derive_sum : forall (i n m : nat) (f : nat -> R -> R),
  (i <= m)%nat -> (forall k, nth_differentiable n (f k)) ->
  ⟦ Der ^ n ⟧ (λ x, ∑ i m (λ k, f k x)) = (λ x, ∑ i m (λ k, (⟦ Der ^ n ⟧ (f k)) x)).
Proof.
  intros i n m f H1 H2. induction n as [| k IH].
  - simpl. reflexivity.
  - simpl.
    rewrite IH.
    2 : {
      intros l. destruct k.
      - exists (f l). simpl. reflexivity.
      - apply nth_differentiable_S_imp_nth_differentiable; [lia | apply H2].
    }
    rewrite Derive_sum; auto.
    intros l.
    specialize (H2 l).
    apply nth_differentiable_imp_differentiable with (n := 1%nat); try lia.
    apply nth_Derive_nth_differentiable with (n := k).
    replace (k + 1)%nat with (S k) by lia.
    apply H2.
Qed.

Lemma nth_Derive_at_sum : forall (i n m : nat) (a : R) (f : nat -> R -> R),
  (i <= m)%nat -> (forall k, nth_differentiable n (f k)) ->
  ⟦ Der ^ n a ⟧ (λ x, ∑ i m (λ k, f k x)) = (∑ i m (λ k, ⟦ Der ^ n a ⟧ (f k))).
Proof.
  intros i n m a f H1 H2.
  unfold nth_Derive_at.
  rewrite nth_Derive_sum; auto.
Qed.

Lemma Derive_mult_const : forall f c,
  differentiable f ->
  ⟦ Der ⟧ (λ x, c * f x) = (λ x, c * (⟦ Der ⟧ f) x).
Proof.
  intros f c H1. pose proof theorem_10_5' f (⟦ Der ⟧ f) c ltac:(apply Derive_spec; auto) as H2.
  apply Derive_spec in H2; auto.
  apply differentiable_mult_const_l; auto.
Qed.

Lemma nth_Derive_mult_const : forall n f c,
  nth_differentiable n f ->
  ⟦ Der ^ n ⟧ (λ x, c * f x) = (λ x, c * (⟦ Der ^ n ⟧ f) x).
Proof.
  intros n f c H1. induction n as [| k IH].
  - simpl. extensionality x. lra.
  - simpl. rewrite IH.
    -- rewrite Derive_mult_const; auto.
       apply nth_differentiable_imp_differentiable with (n := 1%nat); try lia.
       apply nth_Derive_nth_differentiable with (n := k).
       replace (k + 1)%nat with (S k) by lia. auto.
    -- destruct k.
       --- exists f. simpl. reflexivity.
       --- apply nth_differentiable_S_imp_nth_differentiable; [lia | apply H1].
Qed.

Lemma nth_Derive_at_mult_const : forall n a f c,
  nth_differentiable n f ->
  ⟦ Der ^ n a ⟧ (λ x, c * f x) = c * (⟦ Der ^ n a ⟧ f).
Proof.
  intros n a f c H1.
  unfold nth_Derive_at.
  rewrite nth_Derive_mult_const; auto.
Qed.

Lemma nth_Derive_pow : forall k n, (k <= n)%nat ->
  ⟦ Der ^ k ⟧ (fun x => x ^ n) = (fun x => (n! / (n-k)!) * x ^ (n - k)).
Proof.
  intros k n H1.
  apply nth_derivative_of_function_unique with (f := fun x => x ^ n) (n := k).
  - apply nth_derivative_nth_Derive. apply nth_differentiable_pow.
  - apply nth_derivative_pow. apply H1.
Qed.

Lemma nth_Derive_at_pow : forall k n a, (k <= n)%nat ->
  ⟦ Der ^ k a ⟧ (fun x => x ^ n) = (n! / (n - k)!) * a ^ (n - k).
Proof.
  intros k n a H1.
  pose proof nth_Derive_pow k n H1 as H2.
  unfold nth_Derive_at.
  rewrite H2.
  simpl.
  lra.
Qed.

Lemma nth_Derive_pow_gt : forall k n, (k > n)%nat ->
  ⟦ Der ^ k ⟧ (fun x => x ^ n) = (fun x => 0).
Proof.
  intros k n H1.
  apply nth_derivative_of_function_unique with (f := fun x => x ^ n) (n := k).
  - apply nth_derivative_nth_Derive. apply nth_differentiable_pow.
  - apply nth_derivative_pow_gt. apply H1.
Qed.

Lemma nth_Derive_at_pow_gt : forall k n a, (k > n)%nat ->
  ⟦ Der ^ k a ⟧ (fun x => x ^ n) = 0.
Proof.
  intros k n a H1.
  pose proof nth_Derive_pow_gt k n H1 as H2.
  unfold nth_Derive_at.
  rewrite H2.
  simpl.
  lra.
Qed.

Lemma differentiable_mult : forall f g,
  differentiable f -> differentiable g -> differentiable (λ x, f x * g x).
Proof.
  intros f g H1 H2. pose proof differentiable_imp_exists_derivative f H1 as [f' H3].
  pose proof differentiable_imp_exists_derivative g H2 as [g' H4].
  apply derivative_imp_differentiable with (f' := (λ x, f' x * g x + f x * g' x)); auto.
  apply theorem_10_4_b; auto.
Qed.

Lemma differentiable_comp : forall f g,
  differentiable f -> differentiable g ->
  differentiable (λ x, f (g x)).
Proof.
  intros f g H1 H2. pose proof differentiable_imp_exists_derivative f H1 as [f' H3].
  pose proof differentiable_imp_exists_derivative g H2 as [g' H4].
  apply derivative_imp_differentiable with (f' := (λ x, f' (g x) * g' x)); auto.
  apply chain_rule; auto.
Qed.

Lemma differentiable_id : differentiable (λ x, x).
Proof.
  apply derivative_imp_differentiable with (f' := λ x, 1).
  apply theorem_10_2.
Qed.

Lemma nth_derivative_shift : forall n f fn' c,
  ⟦ der^n ⟧ f = fn' ->  ⟦ der^n ⟧ (λ x, f (x - c)) = (λ x, fn' (x - c)).
Proof.
  induction n as [| k IH]; intros f fn' c H1.
  - simpl in *. subst. reflexivity.
  - simpl in *. destruct H1 as [f' [H2 H3]].
    exists (λ x, f' (x - c)). split; auto.
    intros x. unfold derivative_at.
    replace (λ h, (f (x + h - c) - f (x - c)) / h) with (λ h, (f (x - c + h) - f (x - c)) / h).
    2 : { extensionality h. replace (x + h - c) with (x - c + h) by lra. reflexivity. }
    apply H2.
Qed.

Lemma nth_differentiable_shift : forall n f c,
  nth_differentiable n f -> nth_differentiable n (λ x, f (x - c)).
Proof.
  induction n as [| k IH]; intros f c H1.
  - exists (λ x, f (x - c)). reflexivity.
  - destruct H1 as [fn' [f' [H2 H3]]].
    exists (λ x, fn' (x - c)). simpl.
    exists (λ x, f' (x - c)). split.
    -- intros x. unfold derivative_at.
       replace (λ h, (f (x + h - c) - f (x - c)) / h) with (λ h, (f (x - c + h) - f (x - c)) / h).
       2 : { extensionality h. replace (x + h - c) with (x - c + h) by lra. reflexivity. }
       apply H2.
    -- apply nth_derivative_shift; auto.
Qed.

Lemma differentiable_shift : forall f c,
  differentiable f -> differentiable (λ x, f (x - c)).
Proof.
  intros f c H.
  apply nth_differentiable_imp_differentiable with (n := 1%nat).
  - lia.
  - apply nth_differentiable_shift.
    apply differentiable_imp_exists_derivative in H.
    destruct H as [f' Hf'].
    exists f'. exists f'. split; auto. simpl. auto.
Qed.

Lemma nth_differentiable_pow_shift : forall k i a,
  nth_differentiable k (λ x, (x - a) ^ i).
Proof.
  intros k i a.
  change (λ x, (x - a) ^ i) with (λ x, (λ y, y ^ i) (x - a)).
  apply nth_differentiable_shift.
  apply nth_differentiable_pow.
Qed.

Lemma nth_derivative_pow_shift_gt : forall k i a,
  (k > i)%nat -> ⟦ der^k ⟧ (λ x, (x - a) ^ i) = (λ _, 0).
Proof.
  intros k i a Hki.
  apply (nth_derivative_shift k (λ y, y^i) (λ _, 0) a). 
  apply nth_derivative_pow_gt; auto.
Qed.

Lemma nth_Derive_Derive_comm : forall n f,
  nth_differentiable (S n) f ->
  ⟦ Der ^ n ⟧ (⟦ Der ⟧ f) = ⟦ Der ⟧ (⟦ Der ^ n ⟧ f).
Proof.
  intros n f H1. induction n as [| k IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
    destruct H1 as [f'' [f' [H2 H3]]].
    assert (nth_differentiable k f') as [fk' H4].
    { apply nth_differentiable_le with (m := S k); try lia. exists f''; auto. }
    exists fk', f'; split; auto.
Qed.

Lemma nth_Derive_shift : forall n f fn' c,
  nth_differentiable n f ->
  ⟦ Der ^ n ⟧ f = fn' ->  ⟦ Der ^ n ⟧ (λ x, f (x - c)) = (λ x, fn' (x - c)).
Proof.
  intros n f fn' c H1 H2. apply nth_Derive_spec in H2; auto.
  apply nth_Derive_spec. apply nth_differentiable_shift; auto.
  apply nth_derivative_shift; auto.
Qed.

Lemma nth_Derive_at_shift : forall n a f fn' c,
  nth_differentiable n f ->
  ⟦ Der ^ n ⟧ f = fn' ->
  ⟦ Der ^ n a ⟧ (λ x, f (x - c)) = fn' (a - c).
Proof.
  intros n a f fn' c H1 H2.
  unfold nth_Derive_at.
  rewrite nth_Derive_shift with (fn' := fn'); auto.
Qed.

Lemma nth_Derive_pow_shift : forall k n c,
  (k <= n)%nat ->
  ⟦ Der ^ k ⟧ (fun x => (x - c) ^ n) = (fun x => (n! / (n - k)!) * (x - c) ^ (n - k)).
Proof.
  intros k n c H1.
  apply nth_Derive_shift with 
    (f := fun x => x ^ n) 
    (fn' := fun x => (n! / (n - k)!) * x ^ (n - k)).
  - apply nth_differentiable_pow.
  - apply nth_Derive_pow; auto.
Qed.

Lemma nth_Derive_Derive : forall n f,
  nth_differentiable (S n) f ->
  ⟦ der ^ n ⟧ (⟦ Der ⟧ f) = ⟦ Der ^ (S n) ⟧ f.
Proof.
  intros n f. generalize dependent f. induction n as [| k IH]; try reflexivity.
  intros f H1. simpl. exists (⟦ Der ⟧ ⟦ Der ⟧ f); split.
  - apply Derive_spec; auto. apply nth_differentiable_imp_differentiable with (n := 1%nat); try lia.
    apply nth_differentiable_le with (m := S k); try lia.
    apply nth_differentiable_Derive; auto.
- specialize (IH (⟦ Der ⟧ f)). rewrite nth_Derive_Derive_comm in IH; auto. 
  repeat rewrite Derive_nth_Derive in *. apply IH; auto. 
  apply nth_differentiable_Derive; auto.
Qed.

Lemma nth_Derive_Derive_on_comm : forall n f D,
  nth_differentiable_on (S n) f D ->
  ⟦ Der ^ n ⟧ (⟦ Der ⟧ f D) D = ⟦ Der ⟧ (⟦ Der ^ n ⟧ f D) D.
Proof.
  intros n f D H1. induction n as [| k IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
    destruct H1 as [fn' [f' [H2 H3]]].
    assert (nth_differentiable_on k f' D) as [fk' H4].
    { apply nth_differentiable_on_le with (m := S k); try lia. exists fn'; auto. }
    exists fk', f'; split; auto.
Qed.

Lemma nth_Derive_Derive_on : forall n f D,
  nth_differentiable_on (S n) f D ->
  ⟦ der ^ n ⟧ (⟦ Der ⟧ f D) D = ⟦ Der ^ (S n) ⟧ f D.
Proof.
  intros n f D. generalize dependent f. induction n as [| k IH]; try reflexivity.
  - intros f H1 x H2. reflexivity.
  - intros f H1. simpl. exists (⟦ Der ⟧ (⟦ Der ⟧ f D) D). split.
    -- apply Derive_on_imp_derivative_on; auto.
       apply nth_differentiable_on_imp_differentiable_on with (n := 1%nat); try lia.
       apply nth_differentiable_on_le with (m := S k); try lia.
       apply nth_differentiable_on_Derive; auto.
    -- specialize (IH (⟦ Der ⟧ f D)). rewrite nth_Derive_Derive_on_comm in IH; auto.
       apply IH. apply nth_differentiable_on_Derive; auto.
Qed.

Lemma Derive_on_spec_at : forall a f f' D,
  interior_point D a ->
  differentiable_on f D ->
  ⟦ der a ⟧ f = f' <-> (⟦ Der ⟧ f D) a = f' a.
Proof.
  intros a f f' D H1 H2. split; intros H3.
  -
  unfold Derive_on.
  assert (H4 : exists g, is_derive_on_or_zero f D g).
  {
    destruct (differentiable_on_imp_exists_derivative_on f D H2) as [g H4].
    exists g. left; auto.
  }
  pose proof (epsilon_spec (inhabits (λ _ : ℝ, 0)) (is_derive_on_or_zero f D) H4) as H5.
  destruct H5 as [H5 | [H5 H6]].
  -- unfold derivative_on in H5.
    assert (H6 : a ∈ D). 
    { destruct H1 as [δ [H6 H7]]. apply H7. solve_R. } 
    specialize (H2 a H6).
    destruct (H5 a H6) as [[H_int H_at] | [[H_left H_at] | [H_right H_at]]].
    + apply (derivative_of_function_at_x_unique f _ f' a); auto.
    + exfalso. pose proof interior_point_not_endpoint D a H1; tauto.
    + exfalso. pose proof interior_point_not_endpoint D a H1; tauto.
  -- exfalso. apply H5. destruct (differentiable_on_imp_exists_derivative_on f D H2) as [h Hh].
    exists h; auto.
  - unfold Derive_on in H3.
    assert (H4 : exists g, is_derive_on_or_zero f D g).
    { destruct (differentiable_on_imp_exists_derivative_on f D H2) as [g H4].
      exists g. left; auto. }
    pose proof (epsilon_spec (inhabits (λ _ : ℝ, 0)) (is_derive_on_or_zero f D) H4) as H5.
    destruct H5 as [H5 | [H5 H6]].
    + (* Branch: Function is differentiable on D *)
      unfold derivative_on in H5.
      assert (Ha : a ∈ D). 
      { destruct H1 as [δ [H1a H1b]]. apply H1b. solve_R. }
      specialize (H5 a Ha).
      destruct H5 as [[H_int H_at] | [[H_left H_at] | [H_right H_at]]].
      * unfold derivative_at in *. replace (f' a) with (epsilon (inhabits (λ _ : ℝ, 0)) (is_derive_on_or_zero f D) a).
        auto.
      * (* Case: Left Endpoint - Contradiction *)
        exfalso. pose proof interior_point_not_endpoint D a H1; tauto.
      * (* Case: Right Endpoint - Contradiction *)
        exfalso. pose proof interior_point_not_endpoint D a H1; tauto.
    + destruct (differentiable_on_imp_exists_derivative_on f D H2) as [g Hg].
        exfalso. apply H5. exists g. auto.
Qed.

Lemma Derive_on_spec_closed : forall a b c f f',
  a < b -> c ∈ [a, b] ->
  ⟦ der ⟧ f [a, b] = f' ->
  (⟦ Der ⟧ f [a, b]) c = f' c.
Proof.
  intros a b c f f' H1 H2 H3.
  unfold Derive_on.
  assert (H4 : exists g, is_derive_on_or_zero f [a, b] g).
  { exists f'. left. auto. }
  pose proof (epsilon_spec (inhabits (λ _ : ℝ, 0)) (is_derive_on_or_zero f [a, b]) H4) as H5.
  destruct H5 as [H5 | [H5 H6]].
  - specialize (H5 c H2).
    specialize (H3 c H2).
    destruct H5 as [[H_int1 H_at1] | [[H_left1 H_at1] | [H_right1 H_at1]]];
    destruct H3 as [[H_int2 H_at2] | [[H_left2 H_at2] | [H_right2 H_at2]]].
    + apply (derivative_of_function_at_x_unique f _ f' c); auto.
    + exfalso. eapply interior_point_not_endpoint; eauto.
    + exfalso. eapply interior_point_not_endpoint; eauto.
    + exfalso. eapply interior_point_not_endpoint; eauto.
    + apply (right_derivative_of_function_at_x_unique f _ f' c); auto.
    + exfalso. eapply not_right_endpoint_closed; eauto. apply is_right_endpoint_closed; auto.
      apply is_left_endpoint_closed in H_left1; auto. apply is_right_endpoint_closed in H_right2; auto.
      lra. 
    + exfalso. eapply interior_point_not_endpoint; eauto.
    + exfalso. eapply not_left_endpoint_closed; eauto. apply is_left_endpoint_closed; auto.
      apply is_right_endpoint_closed in H_right1; auto. apply is_left_endpoint_closed in H_left2; auto.
      lra.
    + apply (left_derivative_of_function_at_x_unique f _ f' c); auto.
  - exfalso. apply H5. exists f'. auto.
Qed.

Lemma lhopital_nth : forall (n : nat) f g a L,
  (n > 0)%nat ->
  (forall k, (k < n)%nat -> exists δ, δ > 0 /\ forall x, x ∈ (a - δ, a + δ) -> x <> a -> ⟦ Der^(S k) x ⟧ g <> 0) ->
  (forall k, (k <= n)%nat -> nth_differentiable k f) ->
  (forall k, (k <= n)%nat -> nth_differentiable k g) ->
  (forall k, (k < n)%nat -> ⟦ lim a ⟧ (⟦ Der^k ⟧ f) = 0) ->
  (forall k, (k < n)%nat -> ⟦ lim a ⟧ (⟦ Der^k ⟧ g) = 0) ->
  ⟦ lim a ⟧ ( (⟦ Der^n ⟧ f) / (⟦ Der^n ⟧ g) ) = L ->
  ⟦ lim a ⟧ ( f / g ) = L.
Proof.
  intros n. 
  induction n as [| k IH]; try lia.
  intros f g a L H0 H1 H2 H3 H4 H5 H6.
  assert ((k = 0)%nat \/ (k > 0)%nat) as [H7 | H7] by lia.
  - subst k. apply theorem_11_9 with (f' := ⟦ Der ⟧ f) (g' := ⟦ Der ⟧ g); auto.
    -- specialize (H4 0%nat ltac:(lia)); auto.
    -- specialize (H5 0%nat ltac:(lia)); auto. 
    -- apply Derive_spec; try reflexivity. specialize (H2 1%nat ltac:(lia)) as H8.
      destruct H8 as [f'' [f' [H10 H11]]]. apply derivative_imp_differentiable with (f' := f'); auto.
    -- apply Derive_spec; try reflexivity. specialize (H3 1%nat ltac:(lia)) as H8.
      destruct H8 as [g'' [g' [H9 H10]]]. apply derivative_imp_differentiable with (f' := g'); auto.
    -- exists 1. split; try lra. intros x H7 _. apply Derive_spec; auto. apply nth_differentiable_imp_differentiable with (n := 1%nat); auto.
    -- exists 1. split; try lra. intros x H7 _. apply Derive_spec; auto. apply nth_differentiable_imp_differentiable with (n := 1%nat); auto.
    -- apply (H1 0%nat); lia.
  - apply theorem_11_9 with (f' := ⟦ Der ⟧ f) (g' := ⟦ Der ⟧ g); auto.
    -- specialize (H4 0%nat ltac:(lia)); auto.
    -- specialize (H5 0%nat ltac:(lia)); auto.
    -- apply Derive_spec; try reflexivity. specialize (H2 1%nat ltac:(lia)) as H8.
       destruct H8 as [f'' [f' [H9 H10]]]. apply derivative_imp_differentiable with (f' := f'); auto.
    -- apply Derive_spec; try reflexivity. specialize (H3 1%nat ltac:(lia)) as H8.
       destruct H8 as [g'' [g' [H9 H10]]]. apply derivative_imp_differentiable with (f' := g'); auto.
    -- exists 1. split; try lra. intros x H8 _. apply Derive_spec; auto. apply nth_differentiable_imp_differentiable with (n := 1%nat); auto.
    -- exists 1. split; try lra. intros x H8 _. apply Derive_spec; auto. apply nth_differentiable_imp_differentiable with (n := 1%nat); auto.
    -- apply (H1 0%nat); lia.
    -- apply IH; auto.
       ++ intros i H8. specialize (H1 (S i) ltac:(lia)) as [δ [H9 H10]].
          exists δ. split; auto. intros x H11 H12. rewrite nth_Derive_Derive_comm.
          rewrite Derive_nth_Derive. apply H10; auto. apply H3. lia.
       ++ intros i H8; apply nth_differentiable_Derive; apply H2; lia.
       ++ intros i H8. apply nth_differentiable_Derive; apply H3; lia.
       ++ intros i H8. rewrite nth_Derive_Derive_comm. rewrite Derive_nth_Derive. apply H4; lia.
          apply H2; lia.
       ++ intros i H8. rewrite nth_Derive_Derive_comm. rewrite Derive_nth_Derive. apply H5; lia.
          apply H3; lia.
       ++ repeat rewrite nth_Derive_Derive_comm. repeat rewrite <- Derive_nth_Derive in H7. auto. apply H3; lia. apply H2; lia.
Qed.

Lemma lhopital_nth_local : forall (n : nat) f g a D L,
  interior_point D a ->
  nth_differentiable_on n f D ->
  nth_differentiable_on n g D ->
  (forall k, (k < n)%nat -> (⟦ Der^k ⟧ f D) a = 0) ->
  (forall k, (k < n)%nat -> (⟦ Der^k ⟧ g D) a = 0) ->
  ⟦ lim a ⟧ ( (⟦ Der^n ⟧ f D) / (⟦ Der^n ⟧ g D) ) = L ->
  (forall k, (k < n)%nat -> exists δ, δ > 0 /\ forall x, x ∈ (a - δ, a + δ) -> x <> a -> (⟦ Der^(S k) ⟧ g D) x <> 0) ->
  ⟦ lim a ⟧ ( f / g ) = L.
Proof.
  intros n f g a D L H1 H2 H3 H4 H5 H6 H0.
  assert (forall k, (k <= n)%nat -> nth_differentiable_on k f D) as H7.
  { intros m H8. apply nth_differentiable_on_le with (m := n); try lia; auto. }
  assert (forall k, (k <= n)%nat -> nth_differentiable_on k g D) as H8.
  { intros m H9. apply nth_differentiable_on_le with (m := n); try lia; auto. }
  generalize dependent g. generalize dependent f.
  induction n as [| k IH]; auto.
  intros f H2 H4 H7 g H3 H5 H6 H0 H8.
  apply theorem_11_9 with (f' := ⟦ Der ⟧ f D) (g' := ⟦ Der ⟧ g D).
  - specialize (H4 0%nat ltac:(lia)). simpl in H4. rewrite <- H4.
    apply theorem_9_1_a.
    apply nth_differentiable_on_imp_differentiable_at with (n := 1%nat) (D := D); auto.
    destruct H1 as [δ [H9 H10]]. apply H10; solve_R. apply H7; lia.
  - specialize (H5 0%nat ltac:(lia)). simpl in H5. rewrite <- H5.
    apply theorem_9_1_a.
    apply nth_differentiable_on_imp_differentiable_at with (n := 1%nat) (D := D); auto.
    destruct H1 as [δ [H9 H10]]. apply H10; solve_R. apply H8; lia.
  - rewrite Derive_on_spec_at; auto. apply nth_differentiable_on_imp_differentiable_on with (n := 1%nat); try lia.
    apply H7; lia.
  - rewrite Derive_on_spec_at; auto. apply nth_differentiable_on_imp_differentiable_on with (n := 1%nat); try lia.
    apply H8; lia.
  - destruct H1 as [δ [H9 H10]]. exists δ. split; auto. intros x H11 H12.
    apply derivative_on_imp_derivative_at' with (D := D).
    -- exists (Rmin (x - (a - δ)) (a + δ - x)). split; [solve_R |]. intros y H13. apply (H10 y ltac:(solve_R)).
    -- apply Derive_on_imp_derivative_on; auto.
       apply nth_differentiable_on_imp_differentiable_on with (n := 1%nat); auto; try lia.
       apply H7. lia.
  - destruct H1 as [δ [H9 H10]]. exists δ. split; auto. intros x H11 H12.
    apply derivative_on_imp_derivative_at' with (D := D).
    -- exists (Rmin (x - (a - δ)) (a + δ - x)). split; [solve_R |]. intros y H13. apply (H10 y ltac:(solve_R)).
    -- apply Derive_on_imp_derivative_on; auto.
       apply nth_differentiable_on_imp_differentiable_on with (n := 1%nat); auto; try lia.
       apply H8. lia.
  - apply (H0 0%nat); lia.
  - apply IH.
    + apply nth_differentiable_on_Derive; auto.
    + intros i H9. rewrite nth_Derive_Derive_on_comm. rewrite Derive_nth_Derive_on.
      apply H4; lia. apply H7; lia.
    + intros i H9. apply nth_differentiable_on_Derive. apply H7; lia.
    + apply nth_differentiable_on_Derive; auto.
    + intros i H9. rewrite nth_Derive_Derive_on_comm. rewrite Derive_nth_Derive_on.
      apply H5; lia. apply H8; lia.
    + repeat rewrite nth_Derive_Derive_on_comm; auto.
    + intros i H9. specialize (H0 (S i) ltac:(lia)). destruct H0 as [δ [H10 H11]].
      exists δ. split; auto. intros x H12 H13.
      rewrite nth_Derive_Derive_on_comm. rewrite Derive_nth_Derive_on.
      apply H11; auto. apply H8; lia.
    + intros i H9. apply nth_differentiable_on_le with (m := k); auto. apply nth_differentiable_on_Derive; auto.
Qed.

Lemma lhopital_nth_open : forall (n : nat) f g a b c L,
  a < c < b ->
  nth_differentiable_on n f (a, b) ->
  nth_differentiable_on n g (a, b) ->
  (forall k, (k < n)%nat -> (⟦ Der^k ⟧ f (a, b)) c = 0) ->
  (forall k, (k < n)%nat -> (⟦ Der^k ⟧ g (a, b)) c = 0) ->
  (forall k, (k < n)%nat -> exists δ, δ > 0 /\ forall x, x ∈ (c - δ, c + δ) -> x <> c -> (⟦ Der^(S k) ⟧ g (a, b)) x <> 0) ->
  ⟦ lim c ⟧ ( (⟦ Der^n ⟧ f (a, b)) / (⟦ Der^n ⟧ g (a, b)) ) = L ->
  ⟦ lim c ⟧ ( f / g ) = L.
Proof.
  intros n f g a b c L H1 H2 H3 H4 H5 H6 H7.
  apply lhopital_nth_local with (D := (a, b)) (n := n); auto.
  apply is_interior_point_open; solve_R.
Qed.

Lemma nth_derivative_on_imp_nth_differentiable_on : forall n f f' D,
  ⟦ der^n ⟧ f D = f' ->
  nth_differentiable_on n f D.
Proof.
  intros n f f' D H.
  unfold nth_differentiable_on.
  exists f'.
  apply H.
Qed.

Lemma interior_point_in : forall D a,
  interior_point D a -> a ∈ D.
Proof.
  intros D a [δ [H1 H2]].
  apply H2. solve_R.
Qed.

Lemma nth_Derive_on_eq_nth_Derive_at_interior : forall n f D a,
  interior_point D a ->
  nth_differentiable_on n f D ->
  nth_differentiable n f ->
  (⟦ Der^n ⟧ f D) a = ⟦ Der^n a ⟧ f.
Proof.
  intros n f D.
  induction n as [| k IH].
  - intros a H1 H2 H3. simpl. reflexivity.
  - intros a H1 H2 H3.
    simpl. unfold nth_Derive_at.
    assert (H4 : nth_differentiable_on k f D).
    { apply nth_differentiable_on_le with (m := S k); try lia; auto. }
    assert (H5 : nth_differentiable k f).
    { apply nth_differentiable_le with (m := S k); try lia; auto. }
    set (g1 := ⟦ Der^k ⟧ f D).
    set (g2 := ⟦ Der^k ⟧ f). pose proof H1 as H0.
    destruct H1 as [δ [H6 H7]].
    assert (H8 : forall x, |x - a| < δ -> g1 x = g2 x).
    {
      intros x H8.
      apply IH; auto.
      - exists (δ - |x - a|). split.
        + solve_R.
        + intros y H9. apply H7.
          replace y with (x + (y - x)) by lra.
          assert (|x + (y - x) - a| <= |x - a| + |y - x|) by (solve_R).
          solve_R.
    }
    assert (H9 : differentiable_at g1 a).
    {
       apply nth_differentiable_on_imp_differentiable_at with (n := 1%nat) (D := D); auto.
       apply interior_point_in; auto. unfold g1. 
       apply nth_Derive_on_nth_differentiable_on.
       replace (k + 1)%nat with (S k) by lia. auto.
    }
    assert (H10 : differentiable_at g2 a).
    {
       apply nth_differentiable_imp_differentiable_at with (n := 1%nat); auto.
       apply nth_Derive_nth_differentiable; auto. replace (k + 1)%nat with (S k) by lia. auto.
    }
    apply Derive_on_spec_at; auto.  
    apply nth_differentiable_on_imp_differentiable_on with (n := 1%nat); try lia. admit.
    apply Derive_spec_at; auto.
    assert (H11 : ⟦ Der a ⟧ g2 = ⟦ der a ⟧ g2).
    { symmetry. apply Derive_spec. auto. }
    rewrite H11.
    apply derivative_at_eq_eventually with (f1 := g1).
    - exists δ. split; auto.
    - reflexivity.
Qed.

Lemma nth_derivative_subset_open : forall n f f' a b c d,
  (a <= c <= d <= b) -> ⟦ der^n ⟧ f (a, b) = f' ->
  ⟦ der^n ⟧ f (c, d) = f'.
Proof.
  intros n. induction n as [| k IH].
  - intros f f' a b c d H1 H2.
    simpl in *.
    intros x H3. apply H2. solve_R.
  - intros f f' a b c d H1 H2.
    simpl in *.
    destruct H2 as [fn' [Hrec Hder]]. 
    exists fn'. split.
    + intros x H3.
      left. split.
      * apply is_interior_point_open; solve_R.
      * specialize (Hrec x ltac:(solve_R)) as [[_ H4] | [[H4 _] | [H4 _]]]; auto.
        -- apply left_interval_endpoint_open in H4; solve_R.
        -- apply right_interval_endpoint_open in H4; solve_R.
    +
      apply IH with (a := a) (b := b); auto.
Qed.

Lemma nth_derivative_on_eq_f' : forall n f f1' f2' D,
  (forall x, x ∈ D -> f1' x = f2' x) ->
  nth_derivative_on n f f1' D ->
  nth_derivative_on n f f2' D.
Proof.
  induction n; intros f f1' f2' D Heq H1.
  - simpl in *. intros x Hx. rewrite <- Heq; auto.
  - simpl in *. destruct H1 as [g [Hder Hnth]].
    exists g. split; auto.
    apply IHn with (f1' := f1'); auto.
Qed.

Lemma nth_derivative_on_unique : forall n f f1' f2' D,
  nth_derivative_on n f f1' D ->
  nth_derivative_on n f f2' D ->
  forall x, x ∈ D -> f1' x = f2' x.
Proof.
  induction n; intros f f1' f2' D H1 H2 x Hx.
  - simpl in *. rewrite <- H1; auto.
  - simpl in *. destruct H1 as [g1 [Hder1 Hnth1]]. destruct H2 as [g2 [Hder2 Hnth2]].
    assert (Heq: forall y, y ∈ D -> g1 y = g2 y).
    { apply derivative_of_function_on_unique with (f := f) (D := D); auto. }
    assert (Hnth2_g1 : nth_derivative_on n g1 f2' D).
    {
      apply nth_derivative_on_eq with (f1 := g2).
      - intros y Hy. symmetry. apply Heq; auto.
      - apply Hnth2.
    }
    eapply IHn; eauto.
Qed.

Lemma nth_Derive_on_is_derivative : forall n f D,
  nth_differentiable_on n f D ->
  nth_derivative_on n f (nth_Derive_on n f D) D.
Proof.
  intros n f D H.
  destruct n.
  - simpl. intros x Hx. reflexivity.
  - simpl.
    exists (Derive_on f D).
    split.
    + apply Derive_on_imp_derivative_on; auto.
      apply nth_differentiable_on_imp_differentiable_on with (n := S n); try lia.
      auto.
    + apply nth_Derive_Derive_on; auto.
Qed.

Lemma nth_Derive_on_spec : forall n f f' D,
  nth_differentiable_on n f D ->
  ⟦ der^n ⟧ f D = f' <-> (forall x, x ∈ D -> ⟦ Der^n ⟧ f D x = f' x).
Proof.
  intros n f f' D H.
  split; intros H1.
  - apply nth_derivative_on_unique with (n := n) (f := f).
    + apply nth_Derive_on_is_derivative; auto.
    + auto.
  - apply nth_derivative_on_eq_f' with (f1' := nth_Derive_on n f D); auto.
    apply nth_Derive_on_is_derivative; auto.
Qed.

Lemma lhopital_nth_at : forall (n : nat) f g a L,
  nth_differentiable_at n f a ->
  nth_differentiable_at n g a ->
  (forall k, (k < n)%nat -> (⟦ Der^k a ⟧ f) = 0) ->
  (forall k, (k < n)%nat -> (⟦ Der^k a ⟧ g) = 0) ->
  (forall k, (k < n)%nat -> exists δ, δ > 0 /\ forall x, x ∈ (a - δ, a + δ) -> x <> a -> (⟦ Der^(S k) ⟧ g) x <> 0) ->
  ⟦ lim a ⟧ ( (⟦ Der^n ⟧ f) / (⟦ Der^n ⟧ g) ) = L ->
  ⟦ lim a ⟧ ( f / g ) = L.
Proof.
  intros n f g a L [δ1 [H1 [fn' H2]]] [δ2 [H3 [gn' H4]]] H5 H6 H7 H8.
  set (δ := Rmin δ1 δ2).
  apply nth_derivative_subset_open with (a := a - δ1) (b := a + δ1) (c := a - δ) (d := a + δ) in H2; [| unfold δ; solve_R].
  apply nth_derivative_subset_open with (a := a - δ2) (b := a + δ2) (c := a - δ) (d := a + δ) in H4; [| unfold δ; solve_R].
  assert (H9 : nth_differentiable_on n f (a - δ, a + δ)).
  { apply nth_derivative_on_imp_nth_differentiable_on with (f' := fn'); auto. }
  assert (H10 : nth_differentiable_on n g (a - δ, a + δ)).
  { apply nth_derivative_on_imp_nth_differentiable_on with (f' := gn'); auto. }
  assert (H11 : forall k, (k < n)%nat -> (⟦ Der^k ⟧ f (a - δ, a + δ)) a = 0).
  {
    intros k H11. set (D := (a - δ, a + δ)).
    assert (H12 : interior_point D a).
    { apply is_interior_point_open; unfold δ; solve_R. }
    assert (H13: (⟦ Der^k ⟧ f D) a = ⟦ Der^k a ⟧ f).
    {
      admit.
    }
    rewrite H13; auto.
  }
  assert (H12 : forall k, (k < n)%nat -> (⟦ Der^k ⟧ g (a - δ, a + δ)) a = 0).
  { admit. }
  assert (H13 : forall k, (k < n)%nat -> exists δ0, δ0 > 0 /\ forall x, x ∈ (a - δ0, a + δ0) -> x <> a -> (⟦ Der^(S k) ⟧ g (a - δ, a + δ)) x <> 0).
  { admit. }
  assert (H14 : ⟦ lim a ⟧ ( (⟦ Der^n ⟧ f (a - δ, a + δ)) / (⟦ Der^n ⟧ g (a - δ, a + δ)) ) = L).
  { admit. }
  apply lhopital_nth_open with (n := n) (a := a - δ) (b := a + δ) (c := a); auto. unfold δ; solve_R.
Admitted.

Lemma nth_differentiable_imp_nth_differentiable_at : forall n f a,
  nth_differentiable n f -> nth_differentiable_at n f a.
Proof.
  intros n f a [f' H1].
  exists 1; split; try lra.
  exists f'.
  generalize dependent f.
  induction n as [| k IH].
  - intros f H1 x H2.
    rewrite H1.
    reflexivity.
  - intros f [f'' [H1 H2]].
    exists f''; split.
    + intros x H3.
      left; split; auto. apply is_interior_point_open; solve_R.
    + apply IH; auto.
Qed.