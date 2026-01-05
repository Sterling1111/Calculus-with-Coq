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
  | S k => exists fk, nth_derivative k f fk /\ derivative fk fn'
  end.

Definition nth_differentiable (n : nat) (f : R -> R) : Prop :=
  exists fn', nth_derivative n f fn'.

Fixpoint nth_derivative_on (n : nat) (f fn' : R -> R) (D : Ensemble R) : Prop :=
  match n with
  | 0   => forall x, x ∈ D -> f x = fn' x
  | S k => exists fk, nth_derivative_on k f fk D /\ derivative_on fk fn' D
  end.

Definition nth_derivative_at (n : nat) (f fn' : R -> R) (a : R) : Prop :=
  match n with
  | 0   => f a = fn' a
  | S k => exists δ (fk : R -> R),
             δ > 0 /\
             nth_derivative_on k f fk (fun x => a - δ < x < a + δ) /\
             derivative_at fk fn' a
  end.

Definition nth_derivative_at_right (n : nat) (f fn' : R -> R) (a : R) : Prop :=
  match n with
  | 0   => f a = fn' a
  | S k => exists δ (fk : R -> R),
             δ > 0 /\
             nth_derivative_on k f fk (fun x => a <= x < a + δ) /\
             derivative_at_right fk fn' a
  end.

Definition nth_derivative_at_left (n : nat) (f fn' : R -> R) (a : R) : Prop :=
  match n with
  | 0   => f a = fn' a
  | S k => exists δ (fk : R -> R),
             δ > 0 /\
             nth_derivative_on k f fk (fun x => a - δ < x <= a) /\
             derivative_at_left fk fn' a
  end.

Definition nth_differentiable_at (n : nat) (f : R -> R) (a : R) : Prop :=
  exists fn', nth_derivative_at n f fn' a.

Definition nth_differentiable_at_right (n : nat) (f : R -> R) (a : R) : Prop :=
  exists fn', nth_derivative_at_right n f fn' a.

Definition nth_differentiable_at_left (n : nat) (f : R -> R) (a : R) : Prop :=
  exists fn', nth_derivative_at_left n f fn' a.

Definition nth_differentiable_on (n : nat) (f : R -> R) (D : Ensemble R) : Prop :=
  exists fn', nth_derivative_on n f fn' D.

Definition is_derivative_at_limit (f : R -> R) (x : R) (L : R) : Prop :=
  ⟦ lim 0 ⟧ (fun h => (f (x + h) - f x) / h) = L.

Definition is_derivative_at_right_limit (f : R -> R) (x L : R) : Prop :=
  ⟦ lim 0⁺ ⟧ (fun h => (f (x + h) - f x) / h) = L.

Definition is_derivative_at_left_limit (f : R -> R) (x L : R) : Prop :=
  ⟦ lim 0⁻ ⟧ (fun h => (f (x + h) - f x) / h) = L.

Definition is_derive_limit_or_zero (f : R -> R) (x L : R) : Prop :=
  (is_derivative_at_limit f x L) \/ (~differentiable_at f x /\ L = 0).

Definition is_derive_right_limit_or_zero (f : R -> R) (x L : R) : Prop :=
  (is_derivative_at_right_limit f x L) \/
  (~differentiable_at_right f x /\ L = 0).

Definition is_derive_left_limit_or_zero (f : R -> R) (x L : R) : Prop :=
  (is_derivative_at_left_limit f x L) \/
  (~differentiable_at_left f x /\ L = 0).

Definition derive_at (f : R -> R) (x : R) : R :=
  epsilon (inhabits 0) (is_derive_limit_or_zero f x).

Definition derive_at_right (f : R -> R) (x : R) : R :=
  epsilon (inhabits 0) (is_derive_right_limit_or_zero f x).

Definition derive_at_left (f : R -> R) (x : R) : R :=
  epsilon (inhabits 0) (is_derive_left_limit_or_zero f x).

Definition derive (f : R -> R) : R -> R :=
  fun x => derive_at f x.

Fixpoint nth_derive (n:nat) (f : R -> R) : R -> R :=
  match n with
  | 0   => f
  | S k => derive (nth_derive k f)
  end.

Definition nth_derive_at (n:nat) (f : R -> R) (a : R) : R :=
  nth_derive n f a.

Definition is_derive_on_limit_at_point (f : R -> R) (D : Ensemble R) (x y : R) : Prop :=
  (interior_point D x /\ y = derive_at f x) \/
  (left_endpoint D x  /\ y = derive_at_right f x) \/
  (right_endpoint D x /\ y = derive_at_left f x) \/
  (~(interior_point D x) /\ ~(left_endpoint D x) /\ ~(right_endpoint D x) /\ y = 0).

Definition derive_on (f : R -> R) (D : Ensemble R) : R -> R :=
  fun x => epsilon (inhabits 0) (is_derive_on_limit_at_point f D x).

Fixpoint nth_derive_on (n : nat) (f : R -> R) (D : Ensemble R) : R -> R :=
  match n with
  | 0   => f
  | S k => derive_on (nth_derive_on k f D) D
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

  Notation "⟦ 'der' ^ n a ⁺ ⟧ f = fn'" := (nth_derivative_at_right n f fn' a)
    (at level 70, n at level 0, f at level 0, no associativity,
    format "⟦  'der' ^ n  a ⁺  ⟧  f  =  fn'") : derivative_scope.

  Notation "⟦ 'der' ^ n a ⁻ ⟧ f = fn'" := (nth_derivative_at_left n f fn' a)
    (at level 70, n at level 0, f at level 0, no associativity,
    format "⟦  'der' ^ n  a ⁻  ⟧  f  =  fn'") : derivative_scope.

  Notation "⟦ 'Der' ⟧ f" := (derive f)
    (at level 70, f at level 0, no associativity, format "⟦  'Der'  ⟧  f") : derivative_scope.

  Notation "⟦ 'Der' a ⁺ ⟧ f" := (derive_at_right f a)
    (at level 70, a at level 9, f at level 0, no associativity, format "⟦  'Der'  a ⁺  ⟧  f") : derivative_scope.

  Notation "⟦ 'Der' a ⁻ ⟧ f" := (derive_at_left f a)
    (at level 70, a at level 9, f at level 0, no associativity, format "⟦  'Der'  a ⁻  ⟧  f") : derivative_scope.

  Notation "⟦ 'Der' a ⟧ f" := (derive_at f a)
    (at level 70, a at level 9, f at level 0, no associativity, format "⟦  'Der'  a  ⟧  f") : derivative_scope.

  Notation "⟦ 'Der' ⟧ f D" := (derive_on f D)
    (at level 70, f at level 0, D at level 0, no associativity, format "⟦  'Der'  ⟧  f  D") : derivative_scope.

  Notation "⟦ 'Der' ^ n ⟧ f" := (nth_derive n f)
    (at level 70, n at level 9, f at level 0, no associativity, format "⟦  'Der' ^ n  ⟧  f") : derivative_scope.

  Notation "⟦ 'Der' ^ n ⟧ f D" := (nth_derive_on n f D)
    (at level 70, n at level 9, f at level 0, D at level 0, no associativity, format "⟦  'Der' ^ n  ⟧  f  D") : derivative_scope.

  Notation "⟦ 'Der' ^ n a ⟧ f" := (nth_derive_at n f a)
    (at level 70,
      n at level 9,
      a at level 9,
      f at level 0,
      no associativity, format "⟦  'Der' ^ n  a  ⟧  f") : derivative_scope.

End DerivativeNotations.

Import DerivativeNotations.

Open Scope derivative_scope.

Lemma differentiable_domain_open : forall a b,
  a < b -> differentiable_domain (a, b).
Proof.
  intros a b H1 x H2.
  left. auto_interval.
Qed.

Lemma differentiable_domain_closed : forall a b,
  a < b -> differentiable_domain [a, b].
Proof.
  intros a b H1 x H2. auto_interval.
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

Lemma derivative_on_subset : forall f f' D1 D2,
  ⟦ der ⟧ f D1 = f' -> differentiable_domain D2 -> D2 ⊆ D1 -> ⟦ der ⟧ f D2 = f'.
Proof.
  intros f f' D1 D2 H1 H2 H3 a H4.
  specialize (H1 a (H3 _ H4)).
  specialize (H2 a H4) as [H2 | [H2 | H2]].
  - left. split; auto. destruct H2 as [d [H5 H6]].
    assert (H7 : interior_point D1 a) by (exists d; split; auto).
    destruct H1 as [[_ H1] | [[H1 _] | [H1 _]]]; auto_interval.
  - right; left. split; auto. destruct H1 as [[H1 H5] | [[H1 H5] | [H1 H5]]]; auto_interval.
    -- apply derivative_at_iff in H5. tauto.
    -- destruct H1 as [δ1 [H6 H7]]. destruct H2 as [δ2 [H8 H9]].
       specialize (H7 (a + Rmin δ1 δ2 / 2)) as [H7 _].
       specialize (H9 (a + Rmin δ1 δ2 / 2)) as [_ H9].
       assert (H10 : (a + Rmin δ1 δ2 / 2) ∈ D2) by (apply H9; solve_R).
       apply H3 in H10. specialize (H7 ltac:(solve_R)). contradiction.
  - right; right. split; auto. destruct H1 as [[H1 H5] | [[H1 H5] | [H1 H5]]]; auto_interval.
    -- apply derivative_at_iff in H5. tauto.
    -- destruct H1 as [δ1 [H6 H7]]. destruct H2 as [δ2 [H8 H9]].
       specialize (H7 (a - Rmin δ1 δ2 / 2)) as [H7 _].
       specialize (H9 (a - Rmin δ1 δ2 / 2)) as [_ H9].
       assert (H10 : (a - Rmin δ1 δ2 / 2) ∈ D2) by (apply H9; solve_R).
       apply H3 in H10. specialize (H7 ltac:(solve_R)). contradiction.
Qed.

Lemma derivative_on_subset_closed : forall f f' a b c d,
  a <= c < d <= b -> ⟦ der ⟧ f [a, b] = f' -> ⟦ der ⟧ f [c, d] = f'.
Proof.
  intros f f' a b c d H1 H2. apply derivative_on_subset with (D1 := [a, b]); auto.  
  - apply differentiable_domain_closed; solve_R.
  - intros x H3. solve_R.
Qed.

Lemma derivative_on_subset_open : forall f f' a b c d,
  a <= c < d <= b -> ⟦ der ⟧ f (a, b) = f' -> ⟦ der ⟧ f (c, d) = f'.
Proof.
  intros f f' a b c d H1 H2. apply derivative_on_subset with (D1 := (a, b)); auto.
  - apply differentiable_domain_open; solve_R.
  - intros x H3. solve_R.
Qed.

Lemma derivative_at_eq : forall f1 f2 f' a,
  (exists δ, δ > 0 /\ forall x, |x - a| < δ -> f1 x = f2 x) ->
  ⟦ der a ⟧ f1 = f' -> ⟦ der a ⟧ f2 = f'.
Proof.
  intros f1 f2 f' a [δ [H1 H2]] H3.
  apply limit_eq with (f1 := fun h => (f1 (a + h) - f1 a) / h).
  - exists δ. split; auto. intros h H4.
    rewrite H2; [| replace ((a + h) - a) with h by lra; solve_abs].
    rewrite H2; [| rewrite Rminus_diag, Rabs_R0; auto].
    reflexivity.
  - apply H3.
Qed.

Lemma derivative_at_eq' : forall f1 f2 f' a,
  (forall x, f1 x = f2 x) ->
  ⟦ der a ⟧ f1 = f' -> ⟦ der a ⟧ f2 = f'.
Proof.
  intros f1 f2 f' a H1 H2.
  apply derivative_at_eq with (f1 := f1); auto.
  exists 1; split; [ lra |]. intros x H3. apply H1.
Qed.

Lemma derivative_at_right_eq : forall f1 f2 f' a,
  (exists δ, δ > 0 /\ forall x, a <= x < a + δ -> f1 x = f2 x) ->
  ⟦ der a ⁺ ⟧ f1 = f' -> ⟦ der a ⁺ ⟧ f2 = f'.
Proof.
  intros f1 f2 f' a [δ [H1 H2]] H3.
  apply limit_right_eq with (f1 := fun h => (f1 (a + h) - f1 a) / h).
  - exists δ. split; auto. intros h H4.
    rewrite H2; [| lra].
    rewrite H2; [| lra].
    reflexivity.
  - apply H3.
Qed.

Lemma derivative_at_left_eq : forall f1 f2 f' a,
  (exists δ, δ > 0 /\ forall x, a - δ < x <= a -> f1 x = f2 x) ->
  ⟦ der a ⁻ ⟧ f1 = f' -> ⟦ der a ⁻ ⟧ f2 = f'.
Proof.
  intros f1 f2 f' a [δ [H1 H2]] H3.
  apply limit_left_eq with (f1 := fun h => (f1 (a + h) - f1 a) / h).
  - exists δ. split; auto. intros h H4.
    rewrite H2; [| lra].
    rewrite H2; [| lra].
    reflexivity.
  - apply H3.
Qed.

Lemma derivative_on_eq : forall f1 f2 f' D,
  (forall x, x ∈ D -> f1 x = f2 x) -> 
  ⟦ der ⟧ f1 D = f' -> ⟦ der ⟧ f2 D = f'.
Proof.
  intros f1 f2 f' D H1 H2 a H3. specialize (H2 a H3).
  destruct H2 as [[H4 H5] | [[H4 H5] | [H4 H5]]].
  - left. split; auto. eapply derivative_at_eq; eauto.
    destruct H4 as [δ [H6 H7]]. exists δ. split; auto.
    intros x H8. apply H1. apply H7. solve_R.
  - right; left. split; auto. eapply derivative_at_right_eq; eauto.
    destruct H4 as [δ [H6 H7]]. exists δ. split; auto.
    intros x H8. apply H1. apply H7. solve_R.
  - right; right. split; auto. eapply derivative_at_left_eq; eauto.
    destruct H4 as [δ [H6 H7]]. exists δ. split; auto.
    intros x H8. apply H1. apply H7. solve_R.
Qed.

Lemma derivative_eq : forall f1 f2 f',
  (forall x, f1 x = f2 x) -> 
  ⟦ der ⟧ f1 = f' -> ⟦ der ⟧ f2 = f'.
Proof.
  intros f1 f2 f' H1 H2.
  intros a. specialize (H2 a).
  apply derivative_at_eq with (f1 := f1); auto.
  exists 1; split; [ lra |]. intros x H3. apply H1.
Qed.

Lemma derivative_on_ext : forall f f1' f2' D,
  (forall x, x ∈ D -> f1' x = f2' x) -> 
  ⟦ der ⟧ f D = f1' -> ⟦ der ⟧ f D = f2'.
Proof.
  intros f f1' f2' D H1 H2 a H3. specialize (H2 a H3).
  destruct H2 as [[H4 H5] | [[H4 H5] | [H4 H5]]];
  [ left | right; left | right; right ]; split; auto.
  - unfold derivative_at in *. rewrite <- H1; auto.
  - unfold derivative_at_right in *. rewrite <- H1; auto.
  - unfold derivative_at_left in *. rewrite <- H1; auto.
Qed.

Lemma differentiable_at_eq : forall f1 f2 a,
  (exists δ, δ > 0 /\ forall x, |x - a| < δ -> f1 x = f2 x) ->
  differentiable_at f1 a -> differentiable_at f2 a.
Proof.
  intros f1 f2 a [δ [H1 H2]] [L H3]. exists L.
  apply limit_eq with (f1 := fun h => (f1 (a + h) - f1 a) / h); auto.
  exists δ. split; auto. intros h H4. specialize (H2 (a + h) ltac:(solve_R)) as H5.
  specialize (H2 a ltac:(solve_R)) as H6. rewrite H5, H6. reflexivity.
Qed.

Lemma differentiable_at_right_eq : forall f1 f2 a,
  (exists δ, δ > 0 /\ forall x, a <= x < a + δ -> f1 x = f2 x) ->
  differentiable_at_right f1 a -> differentiable_at_right f2 a.
Proof.
  intros f1 f2 a [δ [H1 H2]] [L H3]. exists L.
  apply limit_right_eq with (f1 := fun h => (f1 (a + h) - f1 a) / h); auto.
  exists δ. split; auto. intros h H4.
  rewrite H2; [| lra]. rewrite H2; [| lra]. reflexivity.
Qed.

Lemma differentiable_at_left_eq : forall f1 f2 a,
  (exists δ, δ > 0 /\ forall x, a - δ < x <= a -> f1 x = f2 x) ->
  differentiable_at_left f1 a -> differentiable_at_left f2 a.
Proof.
  intros f1 f2 a [δ [H1 H2]] [L H3]. exists L.
  apply limit_left_eq with (f1 := fun h => (f1 (a + h) - f1 a) / h); auto.
  exists δ. split; auto. intros h H4.
  rewrite H2; [| lra]. rewrite H2; [| lra]. reflexivity.
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

Lemma derivative_on_unique : forall f f1' f2' D,
  ⟦ der ⟧ f D = f1' -> ⟦ der ⟧ f D = f2' -> forall x, x ∈ D -> f1' x = f2' x.
Proof.
  intros f f1' f2' D H1 H2 x H3.
  specialize (H1 x H3). specialize (H2 x H3).
  destruct H1 as [[H4 H5] | [[H4 H5] | [H4 H5]]]; destruct H2 as [[H6 H7] | [[H6 H7] | [H6 H7]]]; auto_interval.
  - eapply derivative_at_unique; eauto.
  - eapply derivative_at_right_unique; eauto.
  - eapply derivative_at_left_unique; eauto.
Qed.

Lemma derivative_on_all_closed_imp_derivative : forall f f',
  (forall a b, a < b -> ⟦ der ⟧ f [a, b] = f') -> ⟦ der ⟧ f = f'.
Proof.
  intros f f' H1 x ε H2. specialize (H1 (x - ε) (x + ε) ltac:(solve_R)) as H3.
  specialize (H3 x ltac:(solve_R)) as [[H4  H5] | [[H4 _] | [H4 _]]]; auto_interval.
Qed.

Lemma derivative_on_imp_derivative_at : forall f f' D a,
  interior_point D a -> ⟦ der ⟧ f D = f' -> ⟦ der a ⟧ f = f'.
Proof.
  intros f f' D a H1 H2.
  assert (H3 : a ∈ D) by (destruct H1 as [δ [H3 H4]]; apply H4; solve_R).
  specialize (H2 a H3) as [[H4 H5] | [[H4 H5] | [H4 H5]]]; auto_interval.
Qed.

Lemma derivative_on_imp_derivative_at_right : forall f f' D a,
  left_endpoint D a -> ⟦ der ⟧ f D = f' -> ⟦ der a ⁺ ⟧ f = f'.
Proof.
  intros f f' D a H1 H2.
  assert (H3 : a ∈ D) by (destruct H1 as [δ [H3 H4]]; apply H4; solve_R).
  specialize (H2 a H3) as [[H4 H5] | [[H4 H5] | [H4 H5]]]; auto_interval.
Qed.

Lemma derivative_on_imp_derivative_at_left : forall f f' D a,
  right_endpoint D a -> ⟦ der ⟧ f D = f' -> ⟦ der a ⁻ ⟧ f = f'.
Proof.
  intros f f' D a H1 H2.
  assert (H3 : a ∈ D) by (destruct H1 as [δ [H3 H4]]; apply H4; solve_R).
  specialize (H2 a H3) as [[H4 H5] | [[H4 H5] | [H4 H5]]]; auto_interval.
Qed.

Theorem derivative_unique : forall f f1' f2',
  ⟦ der ⟧ f = f1' -> ⟦ der ⟧ f = f2' -> f1' = f2'.
Proof.
  intros f f1' f2' H1 H2. extensionality x. 
  apply (derivative_at_unique f f1' f2' x); auto.
Qed.

Lemma derivative_at_imp_differentiable_at : forall f f' a,
  ⟦ der a ⟧ f = f' -> differentiable_at f a.
Proof.
  intros f f' a H1. exists (f' a). apply H1.
Qed.

Lemma differentiable_at_imp_derivative_at : forall f a,
  differentiable_at f a -> exists f', ⟦ der a ⟧ f = f'.
Proof.
  intros f a [L H1]. exists (fun _ => L). apply H1.
Qed.

Lemma differentiable_at_right_imp_derivative_at_right : forall f a,
  differentiable_at_right f a -> exists f', ⟦ der a ⁺ ⟧ f = f'.
Proof.
  intros f a [L H1]. exists (fun _ => L). apply H1.
Qed.

Lemma differentiable_at_left_imp_derivative_at_left : forall f a,
  differentiable_at_left f a -> exists f', ⟦ der a ⁻ ⟧ f = f'.
Proof.
  intros f a [L H1]. exists (fun _ => L). apply H1.
Qed.

Lemma derivative_on_imp_differentiable_on : forall f f' D,
  ⟦ der ⟧ f D = f' -> differentiable_on f D.
Proof.
  intros f f' D H1 x H2. specialize (H1 x H2).
  destruct H1 as [[H3 H4] | [[H3 H4] | [H3 H4]]].
  - left. split; auto. exists (f' x). apply H4.
  - right; left. split; auto. exists (f' x). apply H4.
  - right; right. split; auto. exists (f' x). apply H4.
Qed.

Lemma differentiable_on_imp_derivative_on : forall f D,
  differentiable_on f D -> exists f', ⟦ der ⟧ f D = f'.
Proof.
  intros f D H1.
  assert (H2 : forall x, exists y, (x ∈ D -> 
    (interior_point D x /\ ⟦ der x ⟧ f = (fun _ => y)) \/
    (left_endpoint D x /\ ⟦ der x ⁺ ⟧ f = (fun _ => y)) \/
    (right_endpoint D x /\ ⟦ der x ⁻ ⟧ f = (fun _ => y))) /\ (~ x ∈ D -> y = 0)).
  {
    intros x. destruct (classic (x ∈ D)) as [H2 | H2].
    - specialize (H1 x H2) as [[H3 [L H4]] | [[H3 [L H4]] | [H3 [L H4]]]]; exists L; split; tauto.
    - exists 0; split; tauto.
  }
  apply choice in H2 as [f' H3]. exists f'.
  intros x H4. specialize (H3 x) as [H3 _]. apply H3; auto.
Qed.

Lemma derivative_imp_differentiable : forall f f',
  ⟦ der ⟧ f = f' -> differentiable f.
Proof.
  intros f f' H1 x. unfold differentiable_at. exists (f' x). intros ε H2.
  specialize (H1 x ε) as [δ [H3 H4]]; auto. exists δ. split; auto.
Qed.

Lemma differentiable_imp_derivative : forall f,
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

Lemma differentiable_on_subset : forall f D1 D2,
  differentiable_on f D1 -> differentiable_domain D2 -> D2 ⊆ D1 -> differentiable_on f D2.
Proof.
  intros f D1 D2 H1 H2 H3.
  apply differentiable_on_imp_derivative_on in H1 as [f' H1].
  apply derivative_on_imp_differentiable_on with (f' := f').
  apply derivative_on_subset with (D1 := D1); auto.
Qed.

Lemma differentiable_on_subset_closed : forall a b c d f,
  a <= c < d <= b ->
  differentiable_on f [a, b] -> differentiable_on f [c, d].
Proof.
  intros a b c d f H1 H2.
  apply differentiable_on_subset with (D1 := [a, b]); auto.
  - intros x H3. auto_interval.
  - intros x H3. solve_R.
Qed.

Lemma differentiable_on_subset_open : forall a b c d f,
  a <= c < d <= b ->
  differentiable_on f (a, b) -> differentiable_on f (c, d).
Proof.
  intros a b c d f H1 H2.
  apply differentiable_on_subset with (D1 := (a, b)); auto.
  - intros x H3. auto_interval.
  - intros x H3. solve_R.
Qed.

Lemma differentiable_on_eq : forall f1 f2 D,
  (forall x, x ∈ D -> f1 x = f2 x) -> 
  differentiable_on f1 D -> differentiable_on f2 D.
Proof.
  intros f1 f2 D H1 H2.
  apply differentiable_on_imp_derivative_on in H2 as [f' H2].
  apply derivative_on_imp_differentiable_on with (f' := f').
  apply derivative_on_eq with (f1 := f1); auto.
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
  intros x H3.  auto_interval.
Qed.

Lemma derivative_imp_derivative_on_open : forall f f' a b,
  a < b ->
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ f (a, b) = f'.
Proof.
  intros f f' a b H1 H2. apply derivative_imp_derivative_on; auto.
  intros x H3. auto_interval.
Qed.

Lemma derivative_at_imp_derivative_on : forall f f' D,
  differentiable_domain D ->
  (forall x, x ∈ D -> ⟦ der x ⟧ f = f') ->
  ⟦ der ⟧ f D = f'.
Proof.
  intros f f' D H1 H2 x H3.
  specialize (H1 x H3); specialize (H2 x H3).
  destruct H1 as [H1 | [H1 | H1]].
  - left. split; auto.
  - right; left. split; auto. apply derivative_at_iff in H2; tauto.
  - right; right. split; auto. apply derivative_at_iff in H2; tauto.
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
  intros f a [L H1]. apply limit_right_diff_zero_iff_continuous_at_right.
  assert (⟦ lim 0⁺ ⟧ (fun h => (f (a + h) - f a) / h * h) = 0) as H2.
  { replace 0 with (L * 0) at 2 by lra. apply limit_right_mult. 2 : { apply limit_right_id. } auto. }
  apply limit_right_eq with (f1 := fun h => (f (a + h) - f a) / h * h); auto.
  exists 1. split; [ lra | ]. intros x H3. solve_R.
Qed.

Theorem differentiable_at_left_imp_continuous_at_left : forall f a,
  differentiable_at_left f a -> continuous_at_left f a.
Proof.
  intros f a [L H1]. apply limit_left_diff_zero_iff_continuous_at_left.
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

Theorem differentiable_on_imp_continuous_on : forall f D,
  differentiable_on f D -> continuous_on f D.
Proof.
  intros f D H1 x H2.
  specialize (H1 x H2) as [[H3 H4] | [[H3 H4] | [H3 H4]]].
  - apply limit_imp_limit_on.
    apply differentiable_at_imp_continuous_at; auto.
  - apply continuous_at_right_imp_continuous_on; auto.
    -- destruct H3 as [δ [H5 H6]]. exists δ. split; auto.
       intros y H7 H8.
       destruct (classic (x <= y)); auto.
       exfalso. apply (H6 y); auto. solve_R.
    -- apply differentiable_at_right_imp_continuous_at_right; auto.
  - apply continuous_at_left_imp_continuous_on; auto.
    -- destruct H3 as [δ [H5 H6]]. exists δ. split; auto.
       intros y H7 H8.
       destruct (classic (y <= x)); auto.
       exfalso. apply (H6 y); auto. solve_R.
    -- apply differentiable_at_left_imp_continuous_at_left; auto.
Qed.

Lemma differentiable_on_imp_continuous_on_subset : forall f D1 D2,
  differentiable_on f D1 -> differentiable_domain D2 -> D2 ⊆ D1 -> continuous_on f D2.
Proof.
  intros f D1 D2 H1 H2 H3.
  apply differentiable_on_imp_continuous_on.
  apply differentiable_on_subset with (D1 := D1); auto.
Qed.

Theorem differentiable_on_imp_continuous_on_closed : forall f a b,
  a < b -> differentiable_on f [a, b] -> continuous_on f [a, b].
Proof.
  intros f a b H1 H2. apply differentiable_on_imp_continuous_on_subset with (D1 := [a, b]); auto.
  intros x H3. auto_interval.
  intros x H3. solve_R.
Qed.

Theorem differentiable_on_imp_continuous_on_open : forall f a b,
  a < b -> differentiable_on f (a, b) -> continuous_on f (a, b).
Proof.
  intros f a b H1 H2. apply differentiable_on_imp_continuous_on_subset with (D1 := (a, b)); auto.
  intros x H3. auto_interval.
  intros x H3. solve_R.
Qed.

Lemma differentiable_imp_differentiable_on : forall f D,
  differentiable f -> differentiable_domain D -> differentiable_on f D.
Proof.
  intros f D H1 H2 a H3.
  specialize (H2 a H3). specialize (H1 a).
  destruct H2 as [H2 | [H2 | H2]];
  [ left | right; left | right; right ]; split; auto.
  - apply differentiable_at_imp_left_right in H1; tauto.
  - apply differentiable_at_imp_left_right in H1; tauto.
Qed.

Lemma differentiable_on_imp_differentiable_at : forall f D a,
  a ∈ D -> 
  interior_point D a -> 
  differentiable_on f D -> 
  differentiable_at f a.
Proof.
  intros f D a H1 H2 H3.
  specialize (H3 a H1) as [[H4 H5] | [[H4 H5] | [H4 H5]]]; auto_interval.
Qed.

Lemma differentiable_on_imp_differentiable_at_right : forall f D a,
  left_endpoint D a -> differentiable_on f D -> differentiable_at_right f a.
Proof.
  intros f D a H1 H2.
  apply differentiable_on_imp_derivative_on in H2 as [f' H2].
  exists (f' a). eapply derivative_on_imp_derivative_at_right; eauto.
Qed.

Lemma differentiable_on_imp_differentiable_at_left : forall f D a,
  right_endpoint D a -> differentiable_on f D -> differentiable_at_left f a.
Proof.
  intros f D a H1 H2.
  apply differentiable_on_imp_derivative_on in H2 as [f' H2].
  exists (f' a). eapply derivative_on_imp_derivative_at_left; eauto.
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

Lemma differentiable_on_open_iff : forall f D,
  (forall x, x ∈ D -> interior_point D x) ->
  (differentiable_on f D <-> forall x, x ∈ D -> differentiable_at f x).
Proof.
  intros f D H1. split.
  - intros H2 x H3. eapply differentiable_on_imp_differentiable_at; eauto.
  - intros H2 x H3. left. split; auto.
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

Theorem derivative_on_plus : forall f g f' g' D,
  differentiable_domain D ->
  ⟦ der ⟧ f D = f' -> ⟦ der ⟧ g D = g' ->
  ⟦ der ⟧ (f + g) D = f' + g'.
Proof.
  intros f g f' g' D H1 H2 H3 a H4.
  specialize (H1 a H4) as H1; specialize (H2 a H4) as H2; specialize (H3 a H4) as H3.
  
  destruct H1 as [H1 | [H1 | H1]];
  destruct H2 as [H2 | [H2 | H2]];
  destruct H3 as [H3 | [H3 | H3]];
  try auto_interval.
  - left; split; auto. apply derivative_at_plus; auto.
  - right; left; split; auto. apply derivative_at_right_plus; auto.
  - right; right; split; auto. apply derivative_at_left_plus; auto.
Qed.

Theorem derivative_plus : forall f g f' g',
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' ->
  ⟦ der ⟧ (f + g) = f' + g'.
Proof.
  intros f g f' g' H1 H2 a. apply derivative_at_plus; auto. 
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
  specialize (H1 a H4); specialize (H2 a H4); specialize (H3 a H4).
  destruct H1 as [H1 | [H1 | H1]];
  destruct H2 as [H2 | [H2 | H2]];
  destruct H3 as [H3 | [H3 | H3]];
  try auto_interval.
  - left. split; auto. apply derivative_at_minus; tauto.
  - right; left. split; auto. apply derivative_at_right_minus; tauto.
  - right; right. split; auto. apply derivative_at_left_minus; tauto.
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
  ⟦ der ⟧ (f ∙ g) D = (f' ∙ g + f ∙ g').
Proof.
  intros f g f' g' D H1 H2 H3 a H4.
  specialize (H1 a H4); specialize (H2 a H4); specialize (H3 a H4).
  destruct H1 as [H1 | [H1 | H1]];
  destruct H2 as [H2 | [H2 | H2]];
  destruct H3 as [H3 | [H3 | H3]];
  try auto_interval.
  - left. split; auto. apply derivative_at_mult; tauto.
  - right; left. split; auto. apply derivative_at_right_mult; tauto.
  - right; right. split; auto. apply derivative_at_left_mult; tauto.
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
  ⟦ der ⟧ f D = f' ->
  ⟦ der ⟧ (fun x => c * f x) D = (fun x => c * f' x).
Proof.
  intros f f' D c H1 H2 a H3.
  specialize (H1 a H3); specialize (H2 a H3).
  destruct H1 as [H1 | [H1 | H1]];
  destruct H2 as [H2 | [H2 | H2]];
  try auto_interval.
  - left. split; auto. apply derivative_at_mult_const_l; tauto.
  - right; left. split; auto. apply derivative_at_right_mult_const_l; tauto.
  - right; right. split; auto. apply derivative_at_left_mult_const_l; tauto.
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
  ⟦ der a ⟧ f = f' -> f a <> 0 -> ⟦ der a ⟧ (fun x => / f x) = λ x : ℝ, -1 * f' x / f x ^ 2.
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
  ⟦ der a ⁺ ⟧ f = f' -> f a <> 0 -> ⟦ der a ⁺ ⟧ (fun x => / f x) = λ x : ℝ, -1 * f' x / f x ^ 2.
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
  ⟦ der a ⁻ ⟧ f = f' -> f a <> 0 -> ⟦ der a ⁻ ⟧ (fun x => / f x) = λ x : ℝ, -1 * f' x / f x ^ 2.
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
  ⟦ der ⟧ (fun x => / f x) = λ x : ℝ, -1 * f' x / f x ^ 2.
Proof.
  intros f f' H1 H2 a.
  apply derivative_at_inv; auto.
Qed.

Theorem derivative_on_inv : forall f f' D,
  differentiable_domain D ->
  (forall x, x ∈ D -> f x <> 0) ->
  ⟦ der ⟧ f D = f' -> 
  ⟦ der ⟧ (fun x => / f x) D = λ x : ℝ, -1 * f' x / f x ^ 2.
Proof.
  intros f f' D H1 H2 H3 a H4.
  specialize (H1 a H4); specialize (H2 a H4); specialize (H3 a H4).
  destruct H1 as [H1 | [H1 | H1]];
  destruct H3 as [H3 | [H3 | H3]];
  try auto_interval.
  - left. split; auto. apply derivative_at_inv; tauto.
  - right; left. split; auto. apply derivative_at_right_inv; tauto.
  - right; right. split; auto. apply derivative_at_left_inv; tauto.
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
  ⟦ der a ⟧ f = f' -> ⟦ der a ⟧ g = g' -> g a <> 0 -> ⟦ der a ⟧ (fun x => f x / g x) = (fun x => (f' x * g x - g' x * f x) / (g x * g x)).
Proof.
  intros f f' g g' a H1 H2 H3.
  replace (f / g)%f with (f ∙ (fun x => / g x))%f. 2 : { extensionality x. unfold Rdiv. reflexivity. }
  replace (λ x : ℝ, (f' x * g x - g' x * f x) / (g x * g x)) with (fun x => f' x * /g x + (f x * ((-1 * g' x) * / (g x)^2))).
  2 : { extensionality x. assert (g x = 0 \/ g x <> 0) as [H4 | H4] by lra. rewrite H4. simpl. unfold Rdiv. repeat rewrite Rmult_0_l. rewrite Rinv_0. nra. field; lra. }
  apply derivative_at_mult; auto. apply derivative_at_inv; auto.
Qed.

Lemma derivative_at_right_div : forall f f' g g' a,
  ⟦ der a ⁺ ⟧ f = f' -> ⟦ der a ⁺ ⟧ g = g' -> g a <> 0 -> ⟦ der a ⁺ ⟧ (fun x => f x / g x) = (fun x => (f' x * g x - g' x * f x) / (g x * g x)).
Proof.
  intros f f' g g' a H1 H2 H3.
  replace (f / g)%f with (f ∙ (fun x => / g x))%f. 2 : { extensionality x. unfold Rdiv. reflexivity. }
  replace (λ x : ℝ, (f' x * g x - g' x * f x) / (g x * g x)) with (fun x => f' x * /g x + (f x * ((-1 * g' x) * / (g x)^2))).
  2 : { extensionality x. assert (g x = 0 \/ g x <> 0) as [H4 | H4] by lra. rewrite H4. simpl. unfold Rdiv. repeat rewrite Rmult_0_l. rewrite Rinv_0. nra. field; lra. }
  apply derivative_at_right_mult; auto. apply derivative_at_right_inv; auto.
Qed.

Lemma derivative_at_left_div : forall f f' g g' a,
  ⟦ der a ⁻ ⟧ f = f' -> ⟦ der a ⁻ ⟧ g = g' -> g a <> 0 -> ⟦ der a ⁻ ⟧ (fun x => f x / g x) = (fun x => (f' x * g x - g' x * f x) / (g x * g x)).
Proof.
  intros f f' g g' a H1 H2 H3.
  replace (f / g)%f with (f ∙ (fun x => / g x))%f. 2 : { extensionality x. unfold Rdiv. reflexivity. }
  replace (λ x : ℝ, (f' x * g x - g' x * f x) / (g x * g x)) with (fun x => f' x * /g x + (f x * ((-1 * g' x) * / (g x)^2))).
  2 : { extensionality x. assert (g x = 0 \/ g x <> 0) as [H4 | H4] by lra. rewrite H4. simpl. unfold Rdiv. repeat rewrite Rmult_0_l. rewrite Rinv_0. nra. field; lra. }
  apply derivative_at_left_mult; auto. apply derivative_at_left_inv; auto.
Qed.

Theorem derivative_div : forall f f' g g',
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> (forall x, g x <> 0) -> 
  ⟦ der ⟧ (fun x => f x / g x) =(fun x => (f' x * g x - g' x * f x) / (g x * g x)).
Proof.
  intros f f' g g' H1 H2 H3 a.
  apply derivative_at_div; auto.
Qed.

Theorem derivative_on_div : forall f f' g g' D,
  differentiable_domain D ->
  ⟦ der ⟧ f D = f' -> ⟦ der ⟧ g D = g' -> (forall x, x ∈ D -> g x <> 0) -> 
  ⟦ der ⟧ (fun x => f x / g x) D = (fun x => (f' x * g x - g' x * f x) / (g x * g x)).
Proof.
  intros f f' g g' D H1 H2 H3 H4 a H5.
  specialize (H1 a H5); specialize (H2 a H5); specialize (H3 a H5); specialize (H4 a H5).
  destruct H1 as [H1 | [H1 | H1]];
  destruct H2 as [H2 | [H2 | H2]];
  destruct H3 as [H3 | [H3 | H3]];
  try auto_interval.
  - left. split; auto. apply derivative_at_div; tauto.
  - right; left. split; auto. apply derivative_at_right_div; tauto.
  - right; right. split; auto. apply derivative_at_left_div; tauto.
Qed.

Lemma derivative_on_div_open : forall f f' g g' a b,
  a < b ->
  ⟦ der ⟧ f (a, b) = f' -> ⟦ der ⟧ g (a, b) = g' -> (forall x, x ∈ (a, b) -> g x <> 0) ->
  ⟦ der ⟧ (fun x => f x / g x) (a, b) = (fun x => (f' x * g x - g' x * f x) / (g x * g x)).
Proof.
  intros f f' g g' a b H1 H2 H3 H4.
  apply derivative_on_div; auto.
  apply differentiable_domain_open; auto.
Qed.

Lemma derivative_on_div_closed : forall f f' g g' a b,
  a < b ->
  ⟦ der ⟧ f [a, b] = f' -> ⟦ der ⟧ g [a, b] = g' -> (forall x, x ∈ [a, b] -> g x <> 0) ->
  ⟦ der ⟧ (fun x => f x / g x) [a, b] = (fun x => (f' x * g x - g' x * f x) / (g x * g x)).
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
  specialize (H1 a H4); specialize (H2 a H4); specialize (H3 a H4).
  destruct H1 as [H1 | [H1 | H1]];
  destruct H2 as [H2 | [H2 | H2]];
  try auto_interval.
  - left. split; auto. apply derivative_at_comp; tauto.
  - right; left. split; auto. apply derivative_at_right_comp; tauto.
  - right; right. split; auto. apply derivative_at_left_comp; tauto.
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

Lemma derivative_at_sqrt : forall a,
  a > 0 ->
  ⟦ der a ⟧ (fun x => sqrt x) = (fun x => 1 / (2 * sqrt x)).
Proof.
  intros a H1. unfold derivative_at.
  apply limit_eq with (f1 := fun h => 1 / (sqrt (a + h) + sqrt a)).
  - exists a; split; auto. intros h H2.
    assert (sqrt (a + h) > 0) as H3 by (apply sqrt_lt_R0; solve_R).
    assert (sqrt a > 0) as H4 by (apply sqrt_lt_R0; auto).
    apply Rmult_eq_reg_r with (r := sqrt (a + h) + sqrt a); try lra.
    field_simplify; try solve [solve_R].
    repeat rewrite pow2_sqrt; solve_R.
  - replace (1 / (2 * sqrt a)) with (1 / (sqrt a + sqrt a)).
    2 : { pose proof sqrt_lt_R0 a H1 as H2. solve_R. }
    apply limit_div; try solve_lim.
    -- apply limit_plus; try solve_lim.
       apply limit_sqrt_f_x; solve_lim.
    -- pose proof sqrt_lt_R0 a H1. lra.
Qed.

Lemma derivative_at_right_sqrt : forall a,
  a > 0 ->
  ⟦ der a ⁺ ⟧ (fun x => sqrt x) = (fun x => 1 / (2 * sqrt x)).
Proof.
  intros a H1. apply derivative_at_iff. apply derivative_at_sqrt; auto.
Qed.

Lemma derivative_at_left_sqrt : forall a,
  a > 0 ->
  ⟦ der a ⁻ ⟧ (fun x => sqrt x) = (fun x => 1 / (2 * sqrt x)).
Proof.
  intros a H1. apply derivative_at_iff. apply derivative_at_sqrt; auto.
Qed.

Theorem derivative_on_sqrt : forall D,
  differentiable_domain D ->
  (forall x, x ∈ D -> x > 0) ->
  ⟦ der ⟧ (fun x => sqrt x) D = (fun x => 1 / (2 * sqrt x)).
Proof.
  intros D H1 H2 a H3.
  specialize (H1 a H3); specialize (H2 a H3).
  destruct H1 as [H1 | [H1 | H1]];
  try auto_interval.
  - left. split; auto. apply derivative_at_sqrt; auto.
  - right; left. split; auto. apply derivative_at_right_sqrt; auto.
  - right; right. split; auto. apply derivative_at_left_sqrt; auto.
Qed.

Lemma derivative_on_sqrt_open : forall a b,
  0 <= a < b ->
  ⟦ der ⟧ (fun x => sqrt x) (a, b) = (fun x => 1 / (2 * sqrt x)).
Proof.
  intros a b H1.
  apply derivative_on_sqrt.
  - apply differentiable_domain_open; lra.
  - intros x H2. solve_R.
Qed.

Lemma derivative_on_sqrt_closed : forall a b,
  0 < a < b ->
  ⟦ der ⟧ (fun x => sqrt x) [a, b] = (fun x => 1 / (2 * sqrt x)).
Proof.
  intros a b H1.
  apply derivative_on_sqrt.
  - apply differentiable_domain_closed; lra.
  - intros x H2. solve_R.
Qed.

Theorem derivative_at_sqrt_comp : forall f f' a,
  f a > 0 ->
  ⟦ der a ⟧ f = f' ->
  ⟦ der a ⟧ (fun x => sqrt (f x)) = (fun x => f' x / (2 * sqrt (f x))).
Proof.
  intros f f' a H1 H2.
  replace (fun x => f' x / (2 * sqrt (f x))) with ((fun y => (1 / (2 * sqrt y))%R) ∘ f ∙ f')%f.
  2 : { extensionality x. unfold compose. lra. }
  apply derivative_at_comp; auto.
  apply derivative_at_sqrt; auto.
Qed.

Theorem derivative_at_right_sqrt_comp : forall f f' a,
  f a > 0 ->
  ⟦ der a ⁺ ⟧ f = f' ->
  ⟦ der a ⁺ ⟧ (fun x => sqrt (f x)) = (fun x => f' x / (2 * sqrt (f x))).
Proof.
  intros f f' a H1 H2.
  replace (fun x => f' x / (2 * sqrt (f x))) with ((fun y => (1 / (2 * sqrt y))%R) ∘ f ∙ f')%f.
  2 : { extensionality x. unfold compose. lra. }
  apply derivative_at_right_comp; auto.
  apply derivative_at_sqrt; auto.
Qed.

Theorem derivative_at_left_sqrt_comp : forall f f' a,
  f a > 0 ->
  ⟦ der a ⁻ ⟧ f = f' ->
  ⟦ der a ⁻ ⟧ (fun x => sqrt (f x)) = (fun x => f' x / (2 * sqrt (f x))).
Proof.
  intros f f' a H1 H2.
  replace (fun x => f' x / (2 * sqrt (f x))) with ((fun y => (1 / (2 * sqrt y))%R) ∘ f ∙ f')%f.
  2 : { extensionality x. unfold compose. lra. }
  apply derivative_at_left_comp; auto.
  apply derivative_at_sqrt; auto.
Qed.

Lemma derivative_sqrt_comp : forall f f',
  (forall x, f x > 0) ->
  ⟦ der ⟧ f = f' ->
  ⟦ der ⟧ (fun x => sqrt (f x)) = (fun x => f' x / (2 * sqrt (f x))).
Proof.
  intros f f' H1 H2 a.
  apply derivative_at_sqrt_comp; auto.
Qed.

Theorem derivative_on_sqrt_comp : forall f f' D,
  differentiable_domain D ->
  (forall x, x ∈ D -> f x > 0) ->
  ⟦ der ⟧ f D = f' ->
  ⟦ der ⟧ (fun x => sqrt (f x)) D = (fun x => f' x / (2 * sqrt (f x))).
Proof.
  intros f f' D H1 H2 H3.
  replace (fun x => f' x / (2 * sqrt (f x))) with ((fun y => (1 / (2 * sqrt y))%R) ∘ f ∙ f')%f.
  2 : { extensionality x. unfold compose. lra. }
  apply derivative_on_comp; auto.
  intros x H4. apply derivative_at_sqrt. apply H2; auto.
Qed.

Lemma derivative_at_sum : forall (f : nat -> R -> R) (f' : nat -> R -> R) n i a,
  (i <= n)%nat ->
  (forall k, (i <= k <= n)%nat -> ⟦ der a ⟧ (f k) = (f' k)) ->
  ⟦ der a ⟧ (fun x => ∑ i n (fun k => f k x)) = (fun x => ∑ i n (fun k => f' k x)).
Proof.
  intros f f' n i a H1 H2.
  induction n as [| k IH].
  - assert (i = 0)%nat by lia. subst.
    repeat rewrite sum_f_n_n. apply H2. lia.
  - assert (i = S k \/ i <= k)%nat as [H3 | H3] by lia.
    + rewrite H3. replace (λ x : ℝ, ∑ (S k) (S k) λ k0 : ℕ, f' k0 x) with (f' (S k)).
      2 : { extensionality x. rewrite sum_f_n_n; try lia; auto. }
      replace (λ x : ℝ, ∑ (S k) (S k) λ k0 : ℕ, f k0 x) with (f (S k)).
      2 : { extensionality x. rewrite sum_f_n_n; try lia; auto. } auto.
    + replace (λ x : ℝ, ∑ i (S k) λ k0 : ℕ, f' k0 x) with (fun x => (∑ i k (fun k0 => f' k0 x)) + f' (S k) x).
      2 : { extensionality x. rewrite sum_f_i_Sn_f; try lia; auto. }
      replace (λ x : ℝ, ∑ i (S k) λ k0 : ℕ, f k0 x) with (fun x => (∑ i k (fun k0 => f k0 x)) + f (S k) x).
      2 : { extensionality x. rewrite sum_f_i_Sn_f; try lia; auto. }
      apply derivative_at_plus; auto.
      apply IH; auto. intros j H4. apply H2. lia.
Qed.

Lemma derivative_sum : forall (f : nat -> R -> R) (f' : nat -> R -> R) n i,
  (i <= n)%nat ->
  (forall k, (i <= k <= n)%nat -> ⟦ der ⟧ (f k) = (f' k)) ->
  ⟦ der ⟧ (fun x => ∑ i n (fun k => f k x)) = (fun x => ∑ i n (fun k => f' k x)).
Proof.
  intros f f' n i H1 H2 a.
  apply derivative_at_sum; auto. intros k H3. specialize (H2 k H3). auto.
Qed.

Lemma derivative_on_sum : forall (f : nat -> R -> R) (f' : nat -> R -> R) D n i,
  differentiable_domain D ->
  (i <= n)%nat ->
  (forall k, (i <= k <= n)%nat -> ⟦ der ⟧ (f k) D = (f' k)) ->
  ⟦ der ⟧ (fun x => ∑ i n (fun k => f k x)) D = (fun x => ∑ i n (fun k => f' k x)).
Proof.
  intros f f' D n i H1 H2 H3.
  induction n as [| k IH].
  - assert (i = 0)%nat by lia. subst.
    repeat rewrite sum_f_n_n. apply H3; lia.
  - assert (i = S k \/ i <= k)%nat as [H4 | H4] by lia.
    + rewrite H4. replace (λ x : ℝ, ∑ (S k) (S k) λ k0 : ℕ, f' k0 x) with (f' (S k)).
      2 : { extensionality x. rewrite sum_f_n_n; try lia; auto. }
      replace (λ x : ℝ, ∑ (S k) (S k) λ k0 : ℕ, f k0 x) with (f (S k)).
      2 : { extensionality x. rewrite sum_f_n_n; try lia; auto. } 
      apply H3; lia.
    + replace (λ x : ℝ, ∑ i (S k) (λ k0 : ℕ, f' k0 x)) with (fun x => (∑ i k (fun k0 => f' k0 x)) + f' (S k) x).
      2 : { extensionality x. rewrite sum_f_i_Sn_f; try lia; auto. }
      replace (λ x : ℝ, ∑ i (S k) (λ k0 : ℕ, f k0 x)) with (fun x => (∑ i k (fun k0 => f k0 x)) + f (S k) x).
      2 : { extensionality x. rewrite sum_f_i_Sn_f; try lia; auto. }
      apply derivative_on_plus; auto. apply IH; auto. intros j H5. apply H3; lia.
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
    apply differentiable_on_imp_differentiable_at with (D := (a, b)); auto. auto_interval.
  - exists x2. split; auto. apply derivative_at_minimum_point_zero with (a := a) (b := b); auto. 
    unfold minimum_point. split; auto. intros y H14. apply H11. solve_R. 
    apply differentiable_on_imp_differentiable_at with (D := (a, b)); auto. auto_interval.
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
    intros x. left. destruct (H3 x ltac:(auto)) as [[H6 [L H7]] | [[H6 _] | [H6 H7]]]; auto_interval.
    split; auto. exists (L - (f b - f a) / (b - a)). unfold h.
    apply limit_eq with (f1 := (fun h => (f (x + h) - f x) / h - (f b - f a) / (b - a))).
    exists 1. split; try lra. solve_R.
    apply limit_minus; auto. solve_lim.
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
      destruct H2 as [H2 | [H2 | H2]]; auto_interval.
      exists 0; auto.
    - specialize (H2 a ltac:(solve_R)). destruct H2 as [H2 | [H2 | H2]]; auto_interval.
      apply differentiable_at_right_imp_continuous_at_right. exists 0; auto.
    - assert (x = b \/ x < b) as [H6 | H6] by (solve_R).
      -- subst. apply differentiable_at_left_imp_continuous_at_left. specialize (H2 b ltac:(solve_R)). destruct H2 as [H2 | [H2 | H2]]; auto_interval.
          exists 0; auto.
      -- apply differentiable_at_left_imp_continuous_at_left. 
         assert (H7 : x ∈ (a, b)). { solve_R. }
         specialize (H2 x ltac:(solve_R)). destruct H2 as [H2 | [H2 | H2]]; auto_interval.
         apply derivative_at_iff in H0; destruct H0 as [_ H0]. exists 0; auto.
  }
  assert (differentiable_on f (a, x)) as H7.
  {
    intros x0 H7. left. split; auto_interval.
    assert (H8 : x0 ∈ (a, b)). { solve_R. }
    specialize (H2 x0 ltac:(solve_R)) as [H2 | [H2 | H2]]; auto_interval. exists 0; auto.
  }
  pose proof mean_value_theorem f a x H5 H6 H7 as [c [H8 H9]]. specialize (H2 c ltac:(solve_R)). 
  set (f1 := (λ _ : ℝ, (f x - f a) / (x - a))). set (f2 := (λ _ : ℝ, 0)). assert (f1 c = f2 c) as H10.
  {
    destruct H2 as [H2 | [H2 | H2]]; auto_interval.
    apply derivative_at_unique with (f := f); tauto.
  } unfold f1, f2 in H10.
  apply Rmult_eq_compat_r with (r := (x - a)) in H10. field_simplify in H10; lra.
Qed.

Corollary corollary_11_2 : forall f f' g g' a b, 
  a < b -> ⟦ der ⟧ f [a, b] = f' -> ⟦ der ⟧ g [a, b] = g' -> (forall x, x ∈ [a, b] -> f' x = g' x) -> exists c, forall x, x ∈ [a, b] -> f x = g x + c.
Proof.
  intros f f' g g' a b H1 H2 H3 H4. set (h := fun x => f x - g x). assert (⟦ der ⟧ h [a, b] = (λ x, f' x - g' x)) as H6.
  {
    intros x0 H6. unfold h. assert (x0 = a \/ x0 = b \/ (x0 > a /\ x0 < b)) as [H7 | [H7 | H7]] by (solve_R).
    - right; left. split; auto_interval.
      specialize (H2 x0 H6) as [H2 | [H2 | H2]]; specialize (H3 x0 H6) as [H3 | [H3 | H3]]; subst; auto_interval.
      apply derivative_at_right_minus; tauto.
    - right; right. split; auto_interval.
      specialize (H2 x0 H6) as [H2 | [H2 | H2]]; specialize (H3 x0 H6) as [H3 | [H3 | H3]]; subst; auto_interval.
      apply derivative_at_left_minus; tauto.
    - left. split; auto_interval.
      specialize (H2 x0 H6) as [H2 | [H2 | H2]]; specialize (H3 x0 H6) as [H3 | [H3 | H3]]; auto_interval.
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

Theorem MVT : forall f f' a b,
  a < b -> continuous_on f [a, b] -> ⟦ der ⟧ f (a, b) = f' ->
  exists x, x ∈ (a, b) /\ f' x = (f b - f a) / (b - a).
Proof.
  intros f f' a b H1 H2 H3. pose proof mean_value_theorem f a b H1 H2 as [x [H4 H5]].
  - apply derivative_on_imp_differentiable_on with (f' := f') in H3 as H6; auto.
  - exists x; split; auto. specialize (H3 x ltac:(solve_R)). destruct H3 as [[_ H3] | [[H3 _] | [H3 _]]]; auto_interval.
   pose proof derivative_at_unique f f' (fun _ => (f b - f a) / (b - a)) x H3 H5 as H6; rewrite H6; solve_R.
Qed.

Corollary derivative_on_pos_imp_increasing_on : forall f f' a b, 
  a < b -> ⟦ der ⟧ f [a, b] = f' -> (forall x, x ∈ [a, b] -> f' x > 0) -> increasing_on f [a, b].
Proof.
  intros f f' a b H1 H2 H3 x1 x2 H4 H5 H6. 
  assert (H7 : continuous_on f [x1, x2]).
  {
    apply continuous_on_subset_closed with (a := a) (b := b); try solve_R.
    apply differentiable_on_imp_continuous_on_closed; auto.
    apply derivative_on_imp_differentiable_on with (f' := f'); auto.
  }
  assert (H8 : differentiable_on f (x1, x2)).
  {
    apply differentiable_on_subset_open with (a := a) (b := b); try solve_R.
    apply derivative_on_imp_differentiable_on with (f' := f'); auto.
    apply derivative_on_subset with (D1 := [a, b]); auto.
    - apply differentiable_domain_open; solve_R.
    - intros y H8; solve_R.
  }
  pose proof mean_value_theorem f x1 x2 H6 H7 H8 as [x [H9 H10]]. 
  set (h := λ _ : ℝ, (f x2 - f x1) / (x2 - x1)). assert (h x = f' x) as H11.
  {
    apply derivative_at_unique with (f := f) (x := x); auto. 
    apply derivative_on_imp_derivative_at with (D := (x1, x2)); auto_interval.
    apply derivative_on_subset with (D1 := [a, b]); auto.
    - apply differentiable_domain_open; solve_R.
    - intros y H11; solve_R.
  }
  specialize (H3 x ltac:(auto_interval)). unfold h in H11. 
  assert (H12 : (f x2 - f x1) / (x2 - x1) > 0) by lra.
  apply Rmult_gt_compat_r with (r := (x2 - x1)) in H12; field_simplify in H12; lra.
Qed.

Corollary derivative_on_neg_imp_decreasing_on : forall f f' a b, 
  a < b -> ⟦ der ⟧ f [a, b] = f' -> (forall x, x ∈ [a, b] -> f' x < 0) -> decreasing_on f [a, b].
Proof.
  intros f f' a b H1 H2 H3 x1 x2 H4 H5 H6. 
  assert (H7 : continuous_on f [x1, x2]).
  {
    apply continuous_on_subset_closed with (a := a) (b := b); try solve_R.
    apply differentiable_on_imp_continuous_on_closed; auto.
    apply derivative_on_imp_differentiable_on with (f' := f'); auto.
  }
  assert (H8 : differentiable_on f (x1, x2)).
  {
    apply differentiable_on_subset_open with (a := a) (b := b); try solve_R.
    apply derivative_on_imp_differentiable_on with (f' := f'); auto.
    apply derivative_on_subset with (D1 := [a, b]); auto.
    - apply differentiable_domain_open; solve_R.
    - intros y H8; solve_R.
  }
  pose proof mean_value_theorem f x1 x2 H6 H7 H8 as [x [H9 H10]]. 
  set (h := λ _ : ℝ, (f x2 - f x1) / (x2 - x1)). assert (h x = f' x) as H11.
  {
    apply derivative_at_unique with (f := f) (x := x); auto. 
    apply derivative_on_imp_derivative_at with (D := (x1, x2)); try auto_interval.
    apply derivative_on_subset with (D1 := [a, b]); auto.
    - apply differentiable_domain_open; solve_R.
    - intros y H11; solve_R.
  }
  specialize (H3 x ltac:(auto_interval)). unfold h in H11. 
  assert (H12 : (f x2 - f x1) / (x2 - x1) < 0) by lra.
  apply Rmult_lt_compat_r with (r := (x2 - x1)) in H12; field_simplify in H12; lra.
Qed.

Corollary derivative_on_pos_imp_increasing_on_open : forall f f' a b,
  a < b -> continuous_on f [a, b] -> ⟦ der ⟧ f (a, b) = f' ->
  (forall x, x ∈ (a, b) -> f' x > 0) ->
  increasing_on f [a, b].
Proof.
  intros f f' a b H1 H2 H3 H4 x1 x2 H5 H6 H7.
  
  assert (H8 : differentiable_on f (x1, x2)).
  {
    apply differentiable_on_subset with (D1 := (a, b)).
    - apply derivative_on_imp_differentiable_on with (f' := f'); auto.
    - apply differentiable_domain_open; solve_R.
    - intros x H8. solve_R.
  }

  assert (H9 : continuous_on f [x1, x2]).
  { apply continuous_on_subset with (A2 := [a, b]); auto. intros x H9. solve_R. }

  pose proof mean_value_theorem f x1 x2 H7 H9 H8 as [c [H10 H11]].

  assert (H12 : c ∈ (a, b)). { solve_R. }
  specialize (H3 c H12).
  
  assert (f' c = (f x2 - f x1) / (x2 - x1)) as H13.
  {
    destruct H3 as [[_ H3] | [[H3 _] | [H3 _]]]; auto_interval.
    pose proof derivative_at_unique f (fun _ : R => (f x2 - f x1) / (x2 - x1)) f' c H11 H3 as H13.
    simpl in H13. rewrite <- H13. solve_R.
  }
  
  specialize (H4 c H12).
  rewrite H13 in H4.
  apply Rmult_gt_compat_r with (r := (x2 - x1)) in H4; [| lra].
  field_simplify in H4; [| lra].
  lra.
Qed.

Lemma derivative_on_neg_imp_decreasing_on_open : forall f f' a b,
  a < b -> continuous_on f [a, b] -> ⟦ der ⟧ f (a, b) = f' ->
  (forall x, x ∈ (a, b) -> f' x < 0) ->
  decreasing_on f [a, b].
Proof.
  intros f f' a b H1 H2 H3 H4 x1 x2 H5 H6 H7.
  assert (H8 : differentiable_on f (x1, x2)).
  {
    apply differentiable_on_subset with (D1 := (a, b)).
    - apply derivative_on_imp_differentiable_on with (f' := f'); auto.
    - apply differentiable_domain_open; solve_R.
    - intros x H8. solve_R.
  }
  assert (H9 : continuous_on f [x1, x2]).
  { apply continuous_on_subset with (A2 := [a, b]); auto. intros x H9. solve_R. }
  pose proof mean_value_theorem f x1 x2 H7 H9 H8 as [c [H10 H11]].
  assert (H12 : c ∈ (a, b)). { solve_R. }
  specialize (H3 c H12).
  assert (f' c = (f x2 - f x1) / (x2 - x1)) as H13.
  {
    destruct H3 as [[_ H3] | [[H3 _] | [H3 _]]]; auto_interval.
    pose proof derivative_at_unique f (fun _ : R => (f x2 - f x1) / (x2 - x1)) f' c H11 H3 as H13.
    simpl in H13. rewrite <- H13. solve_R.
  }
  specialize (H4 c H12).
  rewrite H13 in H4.
  apply Rmult_lt_compat_r with (r := (x2 - x1)) in H4; [| lra].
  field_simplify in H4; [| lra].
  lra.
Qed.

Theorem cauchy_mean_value_theorem : forall f f' g g' a b,
  a < b -> continuous_on f [a, b] -> continuous_on g [a, b] -> ⟦ der ⟧ f (a, b) = f' -> ⟦ der ⟧ g (a, b) = g' ->
    exists x, x ∈ (a, b) /\ (f b - f a) * g' x = (g b - g a) * f' x.
Proof.
  intros f f' g g' a b H1 H2 H3 H4 H5. 
  set (h := λ x, (g b - g a) * f x - (f b - f a) * g x).
  assert (continuous_on h [a, b]) as H6.
  {
    unfold h.
    apply continuous_on_minus.
    - apply continuous_on_mult_const_l; auto.
    - apply continuous_on_mult_const_l; auto.
  }
  assert (differentiable_on h (a, b)) as H7.
  {
    unfold h.
    apply derivative_on_imp_differentiable_on with (f' := (λ x, (g b - g a) * f' x - (f b - f a) * g' x)).
    apply derivative_on_minus; auto.
    - apply differentiable_domain_open; auto.
    - apply derivative_on_mult_const_l; auto; apply differentiable_domain_open; auto.
    - apply derivative_on_mult_const_l; auto; apply differentiable_domain_open; auto.
  }
  assert (h a = f a * g b - g a * f b) as H8. { unfold h. lra. }
  assert (h b = f a * g b - g a * f b) as H9. { unfold h. lra. }
  assert (h a = h b) as H10 by lra. 
  pose proof rolles_theorem h a b H1 H6 H7 H10 as [x [H11 H12]].
  assert (⟦ der x ⟧ h = (λ x, (g b - g a) * f' x - (f b - f a) * g' x)) as H13.
  { 
    unfold h. apply derivative_at_minus; apply derivative_at_mult_const_l;
    apply derivative_on_imp_derivative_at with (D := (a, b)); auto_interval.
  }
  exists x; split; auto. 
  pose proof (derivative_at_unique h _ _ x H12 H13) as H14. simpl in H14. lra.
Qed.

Theorem cauchy_mvt : forall f f' g g' a b,
  a < b -> continuous_on f [a, b] -> continuous_on g [a, b] -> ⟦ der ⟧ f (a, b) = f' -> ⟦ der ⟧ g (a, b) = g' -> 
    (forall x, x ∈ (a, b) -> g' x <> 0) -> g b <> g a -> exists x, x ∈ (a, b) /\ (f b - f a) / (g b - g a) = f' x / g' x.
Proof.
  intros f f' g g' a b H1 H2 H3 H4 H5 H6 H7. pose proof cauchy_mean_value_theorem f f' g g' a b H1 H2 H3 H4 H5 as [x [H8 H9]].
  exists x; split; auto. solve_R; split; solve_R.
Qed.

Theorem lhopital_0_0_strong : forall f f' g g' a L,
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
  {
    apply derivative_at_imp_differentiable_at in H3.
    apply differentiable_at_imp_continuous_at in H3.
    apply limit_unique with (f := f) (a := a) (L1 := f a) (L2 := 0); auto.
  }
  assert (H13 : g a = 0).
  {
    apply derivative_at_imp_differentiable_at in H4.
    apply differentiable_at_imp_continuous_at in H4.
    apply limit_unique with (f := g) (a := a) (L1 := g a) (L2 := 0); auto.
  }
  intros ε H14. specialize (H11 ε H14) as [δ4 [H15 H16]].
  set (δ := Rmin (Rmin δ1 (Rmin δ2 δ3)) δ4). exists δ; split; [solve_R|].
  intros x H17. assert (a < x \/ x < a) as [H18 | H18] by solve_R.
  - assert (H19 : continuous_on f [a, x]).
    { 
      intros y H19. destruct (Req_dec_T y a) as [H20 | H20].
      - subst y. apply limit_imp_limit_on. apply differentiable_at_imp_continuous_at. exists (f' a). apply H3.
      - apply limit_imp_limit_on. apply differentiable_at_imp_continuous_at. exists (f' y). apply H6; unfold δ in *; solve_R. 
    }
    assert (H20 : continuous_on g [a, x]).
    {
      intros y H20. destruct (Req_dec_T y a) as [H21 | H21].
      - subst y. apply limit_imp_limit_on. apply differentiable_at_imp_continuous_at. exists (g' a). apply H4.
      - apply limit_imp_limit_on. apply differentiable_at_imp_continuous_at. exists (g' y). apply H8; unfold δ in *; solve_R.
    }
    assert (H21 : ⟦ der ⟧ f (a, x) = f').
    { intros y H21. left. split. auto_interval. apply H6; unfold δ in *; solve_R. }
    assert (H22 : ⟦ der ⟧ g (a, x) = g').
    { intros y H22. left. split. auto_interval. apply H8; unfold δ in *; solve_R. }
    assert (H23 : forall y, y ∈ (a, x) -> g' y <> 0).
    { intros y H23. apply H10; unfold δ in *; solve_R. }
    assert (H24 : g x <> g a).
    {
      intro H24. pose proof (rolles_theorem g a x H18 H20) as [c [H25 H26]]; auto.
      - apply derivative_on_imp_differentiable_on with (f' := g'); auto.
      - specialize (H23 c H25). specialize (H22 c H25) as [[ _ H22 ] | [ [ H22 _ ] | [ H22 _ ] ] ]; try solve [ auto_interval ]. 
        pose proof derivative_at_unique g g' (fun _ => 0) c H22 H26 as H27; auto.
    }
    pose proof cauchy_mvt f f' g g' a x H18 H19 H20 H21 H22 H23 H24 as [c [H25 H26]].
    rewrite H12, H13 in H26. rewrite Rminus_0_r, Rminus_0_r in H26.
    specialize (H16 c ltac:(unfold δ in *; solve_R)). solve_R.
  - assert (H19 : continuous_on f [x, a]).
    { 
      intros y H19. destruct (Req_dec_T y a) as [H20 | H20].
      - subst y. apply limit_imp_limit_on. apply differentiable_at_imp_continuous_at. exists (f' a). apply H3.
      - apply limit_imp_limit_on. apply differentiable_at_imp_continuous_at. exists (f' y). apply H6; unfold δ in *; solve_R. 
    }
    assert (H20 : continuous_on g [x, a]).
    {
      intros y H20. destruct (Req_dec_T y a) as [H21 | H21].
      - subst y. apply limit_imp_limit_on. apply differentiable_at_imp_continuous_at. exists (g' a). apply H4.
      - apply limit_imp_limit_on. apply differentiable_at_imp_continuous_at. exists (g' y). apply H8; unfold δ in *; solve_R. 
    }
    assert (H21 : ⟦ der ⟧ f (x, a) = f').
    { intros y H21. left. split. auto_interval. apply H6; unfold δ in *; solve_R. }
    assert (H22 : ⟦ der ⟧ g (x, a) = g').
    { intros y H22. left. split. auto_interval. apply H8; unfold δ in *; solve_R. }
    assert (H23 : forall y, y ∈ (x, a) -> g' y <> 0).
    { intros y H23. apply H10; unfold δ in *; solve_R. }
    assert (H24 : g a <> g x).
    {
      intro H24. pose proof (rolles_theorem g x a H18 H20) as [c [H25 H26]]; auto.
      - apply derivative_on_imp_differentiable_on with (f' := g'); auto.
      - specialize (H23 c H25). specialize (H22 c H25) as [[ _ H22 ] | [ [ H22 _ ] | [ H22 _ ] ] ]; try solve [ auto_interval ]. 
        pose proof derivative_at_unique g g' (fun _ => 0) c H22 H26 as H27; auto.
    }
    pose proof cauchy_mvt f f' g g' x a H18 H19 H20 H21 H22 H23 H24 as [c [H25 H26]].
    rewrite H12, H13 in H26. rewrite Rminus_0_l, Rminus_0_l, Rdiv_neg_neg_eq in H26.
    specialize (H16 c ltac:(unfold δ in *; solve_R)). solve_R.
Qed.

Theorem lhopital_0_0_weak : forall f g f' g' a,
  ⟦ lim a ⟧ f = 0 ->
  ⟦ lim a ⟧ g = 0 ->
  ⟦ der a ⟧ f = f' ->
  ⟦ der a ⟧ g = g' ->
  g' a <> 0 ->
  ⟦ lim a ⟧ (f / g) = (f' a / g' a).
Proof.
  intros f g f' g' a H1 H2 H3 H4 H5.
  assert (H6 : f a = 0).
  {
    apply derivative_at_imp_differentiable_at in H3.
    apply differentiable_at_imp_continuous_at in H3.
    apply limit_unique with (f := f) (a := a) (L1 := f a) (L2 := 0); auto.
  }
  assert (H7 : g a = 0).
  {
    apply derivative_at_imp_differentiable_at in H4.
    apply differentiable_at_imp_continuous_at in H4.
    apply limit_unique with (f := g) (a := a) (L1 := g a) (L2 := 0); auto.
  }
  assert (H8 : ⟦ lim a ⟧ (λ x : ℝ, (g x - g a) / (x - a)) = g' a).
  { 
    replace a with (0 + a) at 1 by lra. rewrite <- limit_shift with (a := 0) (c := a).
    apply limit_eq with (f1 := fun h => (g (a + h) - g a) / h); auto.
    exists 1. split; [lra|].
    intros h H9. replace (h + a - a) with h by lra. rewrite Rplus_comm. reflexivity.
  }
  assert (H9 : ⟦ lim a ⟧ (λ x : ℝ, (f x - f a) / (x - a)) = f' a).
  { 
    replace a with (0 + a) at 1 by lra. rewrite <- limit_shift with (a := 0) (c := a).
    apply limit_eq with (f1 := fun h => (f (a + h) - f a) / h); auto.
    exists 1. split; [lra|].
    intros h H9. replace (h + a - a) with h by lra. rewrite Rplus_comm. reflexivity.
  }
  pose proof limit_neq_neighborhood (fun x => (g x - g a) / (x - a)) a (g' a) 0 H8 H5 as [δ [H10 H11]].
  apply limit_eq with (f1 := fun x => ((f x - f a) / (x - a)) / ((g x - g a) / (x - a))); auto.
  - exists δ. split; auto. intros x [H12 H13]. specialize (H11 x ltac:(solve_R)). solve_R.
  - apply limit_div; auto.
Qed.

Lemma nth_derivative_0 : forall f,
  ⟦ der ^ 0 ⟧ f = f.
Proof.
  intros f. simpl. reflexivity.
Qed.

Lemma nth_derivative_on_0 : forall f D,
  ⟦ der ^ 0 ⟧ f D = f.
Proof.
  intros f D. simpl. intros x H1. reflexivity.
Qed.

Lemma nth_derivative_1 : forall f f',
  ⟦ der ⟧ f = f' -> ⟦ der ^ 1 ⟧ f = f'.
Proof.
  intros f f' H1. simpl. exists f. split; auto.
Qed.

Lemma nth_derivative_on_1 : forall f f' D,
  ⟦ der ⟧ f D = f' -> ⟦ der ^ 1 ⟧ f D = f'.
Proof.
  intros f f' D H1. simpl. exists f. split; auto.
Qed.

Lemma nth_derivative_on_subset : forall n f fn' D1 D2,
  ⟦ der ^ n ⟧ f D1 = fn' -> differentiable_domain D2 -> D2 ⊆ D1 -> ⟦ der ^ n ⟧ f D2 = fn'.
Proof.
  induction n as [| k IH]; intros f fn' D1 D2 H1 H2 H3.
  - simpl in *. intros x H4. apply H1. apply H3; auto.
  - simpl in *. destruct H1 as [fk [H1 H4]].
    exists fk. split.
    + apply IH with (D1 := D1); auto.
    + apply derivative_on_subset with (D1 := D1); auto.
Qed.

Lemma nth_derivative_imp_nth_derivative_on : forall n f fn' D,
  differentiable_domain D ->
  ⟦ der ^ n ⟧ f = fn' -> ⟦ der ^ n ⟧ f D = fn'.
Proof.
  induction n as [| k IH]; intros f fn' D H1 H2.
  - simpl in *. intros x H3. rewrite H2. reflexivity.
  - simpl in *. destruct H2 as [fk [H2 H3]].
    exists fk. split.
    + apply IH; auto.
    + apply derivative_imp_derivative_on; auto.
Qed.

Lemma nth_derivative_on_eq : forall n f1 f2 fn' D,
  (forall x, x ∈ D -> f1 x = f2 x) ->
  ⟦ der ^ n ⟧ f1 D = fn' -> ⟦ der ^ n ⟧ f2 D = fn'.
Proof.
  induction n as [| k IH]; intros f1 f2 fn' D H1 H2.
  - simpl in *. intros x H3. rewrite <- H1; auto.
  - simpl in *. destruct H2 as [fk [H2 H3]].
    exists fk. split; auto.
    eapply IH; eauto.
Qed.

Lemma nth_derivative_at_eq : forall n f1 f2 fn' a,
  (exists δ, δ > 0 /\ forall x, |x - a| < δ -> f1 x = f2 x) ->
  ⟦ der ^ n a ⟧ f1 = fn' -> ⟦ der ^ n a ⟧ f2 = fn'.
Proof.
  intros n f1 f2 fn' a [δ [H1 H2]] H3.
  destruct n as [| k].
  - simpl in *. rewrite <- H3. symmetry. apply H2. solve_R.
  - simpl in *. destruct H3 as [δ1 [fk' [H3 [H4 H5]]]].
    exists (Rmin δ δ1), fk'. repeat split; try solve [ solve_R ].
    apply nth_derivative_on_eq with (f1 := f1).
    + intros x H6. apply H2. solve_R.
    + apply nth_derivative_on_subset with (D1 := (a - δ1, a + δ1)); auto.
      * intros x H6. auto_interval.
      * intros x H6. solve_R.
Qed.

Lemma nth_derivative_on_ext : forall n f f1' f2' D,
  (forall x, x ∈ D -> f1' x = f2' x) -> 
  ⟦ der ^ n ⟧ f D = f1' -> ⟦ der ^ n ⟧ f D = f2'.
Proof.
  intros n f f1' f2' D H1 H2.
  destruct n as [| k].
  - simpl in *. intros x H3. rewrite <- H1; auto.
  - simpl in *. destruct H2 as [fk [H2 H3]].
    exists fk. split; auto.
    eapply derivative_on_ext; eauto.
Qed.

Lemma nth_derivative_on_unique : forall n f fn1' fn2' D,
  ⟦ der ^ n ⟧ f D = fn1' -> ⟦ der ^ n ⟧ f D = fn2' -> forall x, x ∈ D -> fn1' x = fn2' x.
Proof.
  induction n as [| k IH]; intros f fn1' fn2' D H1 H2 x H3.
  - simpl in *. rewrite <- H2; auto. specialize (H1 x H3). auto.
  - simpl in *. destruct H1 as [fk1 [H1 H4]].
    destruct H2 as [fk2 [H2 H5]].
    assert (H6 : forall y, y ∈ D -> fk1 y = fk2 y).
    { eapply IH; eauto. }
    eapply derivative_on_unique; eauto.
    apply derivative_on_eq with (f1 := fk2); auto.
    intros y H7. symmetry. apply H6; auto.
Qed.

Lemma nth_derivative_unique : forall n f fn1' fn2',
  ⟦ der ^ n ⟧ f = fn1' -> ⟦ der ^ n ⟧ f = fn2' -> fn1' = fn2'.
Proof.
  induction n as [| k IH]; intros f fn1' fn2' H1 H2.
  - simpl in H1, H2. subst. reflexivity.
  - simpl in *. destruct H1 as [fk1 [H1 H3]], H2 as [fk2 [H2 H4]].
    assert (fk1 = fk2).
    { eapply IH; eauto. }
    subst fk2.
    eapply derivative_unique; eauto.
Qed.

Lemma nth_derivative_at_ext_val : forall n f f' g' a,
  ⟦ der^n a ⟧ f = f' ->
  f' a = g' a ->
  ⟦ der^n a ⟧ f = g'.
Proof.
  intros n f f' g' a Hder Heq.
  destruct n.
  - simpl in *. rewrite <- Heq. assumption.
  - simpl in *. destruct Hder as [δ [fk [H1 [H2 H3]]]].
    exists δ, fk. repeat split; auto.
    unfold derivative_at in *. rewrite <- Heq. assumption.
Qed.

Lemma nth_derivative_imp_at : forall n f f' a,
  ⟦ der^n ⟧ f = f' ->
  ⟦ der^n a ⟧ f = f'.
Proof.
  induction n; intros f f' a H.
  - simpl in *; subst; auto.
  - simpl in *. destruct H as [fk [H1 H2]].
    exists 1, fk. (* Delta can be anything, say 1 *)
    split; [lra |]. 
    split.
    + apply nth_derivative_imp_nth_derivative_on; auto. apply differentiable_domain_open; lra.
    + unfold derivative_at. apply H2.
Qed.

Lemma nth_differentiable_imp_differentiable : forall n f,
  (n > 0)%nat -> nth_differentiable n f -> differentiable f.
Proof.
  intros n f H1 H2.
  induction n as [| k IH]; try lia.
  destruct k.
  - destruct H2 as [f' H2].
    destruct H2 as [f0 [H2 H3]]. simpl in H2. subst.
    eapply derivative_imp_differentiable; eauto.
  - apply IH; try lia. destruct H2 as [fn H2].
    destruct H2 as [fk [H3 H4]]. exists fk; auto.
Qed.

Lemma nth_differentiable_on_imp_differentiable_on : forall n f D,
  (n > 0)%nat ->
  nth_differentiable_on n f D -> 
  differentiable_on f D.
Proof.
  intros n f D H1 H2.
  induction n as [| k IH]; try lia.
  destruct H2 as [fn' [fk [H3 H4]]].
  destruct k as [| m].
  - apply derivative_on_imp_differentiable_on with (f' := fn').
    apply derivative_on_eq with (f1 := fk); auto.
    intros x H5. rewrite <- H3; auto.
  - apply IH; try lia. exists fk; auto.
Qed.

Lemma nth_differentiable_on_imp_differentiable_at : forall n f D a,
  (n > 0)%nat ->
  a ∈ D -> 
  interior_point D a ->
  nth_differentiable_on n f D -> 
  differentiable_at f a.
Proof.
  intros n f D a H1 H2 H3 H4.
  apply nth_differentiable_on_imp_differentiable_on in H4; auto.
  apply differentiable_on_imp_differentiable_at with (D := D); auto.
Qed.

Lemma nth_derivative_le_differentiable : forall n m f fn,
  (m <= n)%nat -> ⟦ der ^ n ⟧ f = fn -> nth_differentiable m f.
Proof.
  induction n as [| k IH]; intros m f fn H1 H2.
  - assert (H3 : (m = 0)%nat) by lia. rewrite H3.
    exists f. simpl. reflexivity.
  - destruct H2 as [fk [H3 H4]].
    assert ((m <= k)%nat \/ m = S k) as [H5 | H5] by lia.
    + apply IH with (fn := fk); auto.
    + subst m. exists fn. simpl. exists fk. split; auto.
Qed.

Lemma nth_derivative_on_le_differentiable : forall n m f fn D,
  (m <= n)%nat -> ⟦ der ^ n ⟧ f D = fn -> nth_differentiable_on m f D.
Proof.
  induction n as [| k IH]; intros m f fn D H1 H2.
  - assert (H3 : (m = 0)%nat) by lia. subst m.
    exists f. simpl. intros x H3. reflexivity.
  - destruct H2 as [fk [H3 H4]].
    assert ((m <= k)%nat \/ m = S k) as [H5 | H5] by lia.
    + apply IH with (fn := fk); auto.
    + subst m. exists fn. simpl. exists fk. split; auto.
Qed.

Lemma nth_differentiable_succ_imp_differentiable : forall n f,
  nth_differentiable (S n) f -> nth_differentiable n f.
Proof.
  intros n f [fn H1].
  apply nth_derivative_le_differentiable with (n := S n) (fn := fn); auto.
Qed.

Lemma nth_differentiable_on_succ_imp_differentiable_on : forall n f D,
  nth_differentiable_on (S n) f D -> nth_differentiable_on n f D.
Proof.
  intros n f D [fn H1].
  apply nth_derivative_on_le_differentiable with (n := S n) (fn := fn); auto.
Qed.

Lemma nth_derivative_split_end : forall n f fn',
  ⟦ der ^ (S n) ⟧ f = fn' -> exists fn, ⟦ der ^ n ⟧ f = fn /\ ⟦ der ⟧ fn = fn'.
Proof.
  intros n f fn' H1.
  destruct H1 as [fk [H1 H2]].
  exists fk. split; auto.
Qed.

Lemma nth_differentiable_imp_nth_differentiable_at : forall n f a,
  nth_differentiable n f -> nth_differentiable_at n f a.
Proof.
  intros n f a [fn' H1].
  exists fn'.
  destruct n as [| k].
  - simpl in H1. rewrite H1. reflexivity.
  - destruct H1 as [fk [H1 H2]].
    exists 1, fk. split; [lra |].
    split.
    + apply nth_derivative_imp_nth_derivative_on.
      * apply differentiable_domain_open; lra.
      * apply H1.
    + apply H2.
Qed.

Lemma nth_derivative_at_unique : forall n f fn1' fn2' a,
  ⟦ der ^ n a ⟧ f = fn1' -> ⟦ der ^ n a ⟧ f = fn2' -> fn1' a = fn2' a.
Proof.
  induction n as [| k IH]; intros f fn1' fn2' a H1 H2.
  - simpl in *. lra.
  - destruct H1 as [d1 [fk1 [H1 [H3 H4]]]].
    destruct H2 as [d2 [fk2 [H5 [H6 H7]]]].
    assert (H8 : forall x, |x - a| < Rmin d1 d2 -> fk1 x = fk2 x).
    {
      intros x H8.
      apply nth_derivative_on_unique with (n := k) (f := f) (D := (a - Rmin d1 d2, a + Rmin d1 d2)).
      - apply nth_derivative_on_subset with (D1 := (a - d1, a + d1)); auto.
        + intros y Hy. auto_interval.
        + intros y Hy. solve_R.
      - apply nth_derivative_on_subset with (D1 := (a - d2, a + d2)); auto.
        + intros y Hy. auto_interval.
        + intros y Hy. solve_R.
      - solve_R.
    }
    apply derivative_at_unique with (f := fk1); auto.
    apply derivative_at_eq with (f1 := fk2); auto.
    exists (Rmin d1 d2). split; [solve_R |].
    intros x H9. symmetry. apply H8; auto.
Qed.

Lemma nth_derivative_succ_iff : forall n f fn',
  ⟦ der ^ (S n) ⟧ f = fn' <-> exists f', ⟦ der ⟧ f = f' /\ ⟦ der ^ n ⟧ f' = fn'.
Proof.
  induction n as [| k IH]; intros f fn'.
  - simpl. split.
    + intros [fk [H1 H2]]. rewrite H1. exists fn'. split; auto.
    + intros [f' [H1 H2]]. rewrite <- H2.
      exists f. split; auto.
  - simpl. split.
    + intros [fk [H1 H2]].
      apply IH in H1. destruct H1 as [f' [H1 H3]].
      exists f'. split; auto.
      exists fk. split; auto.
    + intros [f' [H1 H2]].
      destruct H2 as [fk [H2 H3]].
      exists fk. split; auto.
      apply IH. exists f'. split; auto.
Qed.

Lemma nth_derivative_on_succ_iff : forall n f fn' D,
  ⟦ der ^ (S n) ⟧ f D = fn' <-> exists f', ⟦ der ⟧ f D = f' /\ ⟦ der ^ n ⟧ f' D = fn'.
Proof.
  induction n as [| k IH]; intros f fn' D.
  - simpl. split.
    + intros [fk [H1 H2]]. exists fn'. split; auto.
      apply derivative_on_eq with (f1 := fk); auto. intros x H3. rewrite H1; auto.
    + intros [f' [H1 H2]]. exists f. split; auto.
      apply derivative_on_ext with (f1' := f'); auto.
  - simpl. split.
    + intros [fk [H1 H2]].
      apply IH in H1. destruct H1 as [f' [H1 H3]].
      exists f'. split; auto.
      exists fk. split; auto.
    + intros [f' [H1 H2]].
      destruct H2 as [fk [H2 H3]].
      exists fk. split; auto.
      apply IH. exists f'. split; auto.
Qed.

Lemma nth_differentiable_at_imp_differentiable_at : forall n f a,
  (n > 0)%nat ->
  nth_differentiable_at n f a ->
  differentiable_at f a.
Proof.
  intros n f a H1 [fn' H2].
  destruct n as [| k].
  - lia.
  - simpl in H2. destruct H2 as [d [fk [H2 [H3 H4]]]].
    destruct k.
    + simpl in H3.
      apply derivative_at_imp_differentiable_at with (f' := fn').
      apply derivative_at_eq with (f1 := fk); auto.
      exists d. split; auto.
      intros x H5. specialize (H3 x ltac:(solve_R)). auto.
    + apply nth_differentiable_on_imp_differentiable_at with (n := S k) (D := (a - d, a + d)); try lia.
      * auto_interval.
      * auto_interval.
      * exists fk. apply H3.
Qed.

Lemma nth_differentiable_at_imp_neighborhood : forall n f a,
  nth_differentiable_at (S n) f a ->
  exists δ, δ > 0 /\ nth_differentiable_on n f (a - δ, a + δ).
Proof.
  intros n f a [fn' H].
  simpl in H. destruct H as [δ [fk [H1 [H2 H3]]]].
  exists δ. split; auto.
  exists fk. auto.
Qed.

Lemma nth_derivative_imp_nth_differentiable : forall n f fn,
  ⟦ der ^ n ⟧ f = fn -> nth_differentiable n f.
Proof.
  intros n f fn H1. exists fn. apply H1.
Qed.

Lemma nth_derivative_on_imp_nth_differentiable_on : forall n f fn D,
  ⟦ der ^ n ⟧ f D = fn -> nth_differentiable_on n f D.
Proof.
  intros n f fn D H1. exists fn. apply H1.
Qed.

Lemma nth_differentiable_on_subset : forall n f D1 D2,
  nth_differentiable_on n f D1 -> differentiable_domain D2 -> D2 ⊆ D1 -> nth_differentiable_on n f D2.
Proof.
  intros n f D1 D2 H1 H2 H3. destruct H1 as [fn' H1].
  apply nth_derivative_on_imp_nth_differentiable_on with (fn := fn'); auto.
  apply nth_derivative_on_subset with (D1 := D1); auto.
Qed.

Lemma nth_derivative_at_imp_nth_differentiable_at : forall n f a fn',
  ⟦ der ^ n a ⟧ f = fn' -> nth_differentiable_at n f a.
Proof.
  intros n f a fn' H1. exists fn'. apply H1.
Qed.

Lemma nth_derivative_plus : forall n f g fn' gn',
  ⟦ der ^ n ⟧ f = fn' -> ⟦ der ^ n ⟧ g = gn' ->
  ⟦ der ^ n ⟧ (f + g) = fn' + gn'.
Proof.
  induction n as [| k IH]; intros f g fn' gn' H1 H2.
  - simpl in *. subst. reflexivity.
  - simpl in *. destruct H1 as [f' [H1 H3]], H2 as [g' [H2 H4]].
    exists (f' + g')%f. split.
    + apply IH; auto.
    + apply derivative_plus; auto.
Qed.

Lemma nth_derivative_on_plus : forall n f g fn' gn' D,
  differentiable_domain D ->
  ⟦ der ^ n ⟧ f D = fn' -> ⟦ der ^ n ⟧ g D = gn' ->
  ⟦ der ^ n ⟧ (f + g) D = fn' + gn'.
Proof.
  induction n as [| k IH]; intros f g fn' gn' D H1 H2 H3.
  - simpl in *. intros x H4. specialize (H2 x H4). specialize (H3 x H4).
    rewrite H2, H3. reflexivity.
  - simpl in *. destruct H2 as [f' [H2 H4]], H3 as [g' [H3 H5]].
    exists (f' + g')%f. split.
    + apply IH; auto.
    + apply derivative_on_plus; auto.
Qed.

Lemma nth_derivative_at_plus : forall n f g fn' gn' a,
  ⟦ der ^ n a ⟧ f = fn' -> ⟦ der ^ n a ⟧ g = gn' ->
  ⟦ der ^ n a ⟧ (f + g) = fn' + gn'.
Proof.
  induction n as [| k IH]; intros f g fn' gn' a H1 H2.
  - simpl in *. subst. lra.
  - simpl in *. destruct H1 as [d1 [fk [H1 [H3 H4]]]].
    destruct H2 as [d2 [gk [H2 [H5 H6]]]].
    exists (Rmin d1 d2), (fk + gk)%f. split; [solve_R |].
    split.
    + apply nth_derivative_on_plus with (D := (a - Rmin d1 d2, a + Rmin d1 d2)).
      * apply differentiable_domain_open; solve_R.
      * apply nth_derivative_on_subset with (D1 := (a - d1, a + d1)); auto;
        [intros x H7; auto_interval | intros x H7; solve_R].
      * apply nth_derivative_on_subset with (D1 := (a - d2, a + d2)); auto;
        [intros x H7; auto_interval | intros x H7; solve_R].
    + apply derivative_at_plus; auto.
Qed.

Lemma nth_derivative_minus : forall n f g fn' gn',
  ⟦ der ^ n ⟧ f = fn' -> ⟦ der ^ n ⟧ g = gn' ->
  ⟦ der ^ n ⟧ (f - g) = (fn' - gn').
Proof.
  induction n as [| k IH]; intros f g fn' gn' H1 H2.
  - simpl in *. subst. reflexivity.
  - simpl in *. destruct H1 as [f' [H1 H3]], H2 as [g' [H2 H4]].
    exists (f' - g')%f. split.
    + apply IH; auto.
    + apply derivative_minus; auto.
Qed.

Lemma nth_derivative_on_minus : forall n f g fn' gn' D,
  differentiable_domain D ->
  ⟦ der ^ n ⟧ f D = fn' -> ⟦ der ^ n ⟧ g D = gn' ->
  ⟦ der ^ n ⟧ (f - g) D = (fn' - gn').
Proof.
  induction n as [| k IH]; intros f g fn' gn' D H1 H2 H3.
  - simpl in *. intros x H4. specialize (H2 x H4). specialize (H3 x H4).
    rewrite H2, H3. reflexivity.
  - simpl in *. destruct H2 as [f' [H2 H4]], H3 as [g' [H3 H5]].
    exists (f' - g')%f. split.
    + apply IH; auto.
    + apply derivative_on_minus; auto.
Qed.

Lemma nth_derivative_at_minus : forall n f g fn' gn' a,
  ⟦ der ^ n a ⟧ f = fn' -> ⟦ der ^ n a ⟧ g = gn' ->
  ⟦ der ^ n a ⟧ (f - g) = fn' - gn'.
Proof.
  induction n as [| k IH]; intros f g fn' gn' a H1 H2.
  - simpl in *. subst. lra.
  - simpl in *. destruct H1 as [d1 [fk [H1 [H3 H4]]]].
    destruct H2 as [d2 [gk [H2 [H5 H6]]]].
    exists (Rmin d1 d2), (fk - gk)%f. split; [solve_R |].
    split.
    + apply nth_derivative_on_minus with (D := (a - Rmin d1 d2, a + Rmin d1 d2)).
      * apply differentiable_domain_open; solve_R.
      * apply nth_derivative_on_subset with (D1 := (a - d1, a + d1)); auto;
        [intros x H7; auto_interval | intros x H7; solve_R].
      * apply nth_derivative_on_subset with (D1 := (a - d2, a + d2)); auto;
        [intros x H7; auto_interval | intros x H7; solve_R].
    + apply derivative_at_minus; auto.
Qed.

Lemma nth_derivative_neg : forall n f fn',
  ⟦ der ^ n ⟧ f = fn' ->
  ⟦ der ^ n ⟧ (- f) = (- fn').
Proof.
  induction n as [| k IH]; intros f fn' H1.
  - simpl in *. subst. reflexivity.
  - simpl in *. destruct H1 as [f' [H1 H2]].
    exists (- f')%f. split.
    + apply IH; auto.
    + apply derivative_neg; auto.
Qed.

Lemma nth_derivative_on_neg : forall n f fn' D,
  differentiable_domain D ->
  ⟦ der ^ n ⟧ f D = fn' ->
  ⟦ der ^ n ⟧ (- f) D = (- fn').
Proof.
  induction n as [| k IH]; intros f fn' D H1 H2.
  - simpl in *. intros x H3. specialize (H2 x H3). rewrite H2. reflexivity.
  - simpl in *. destruct H2 as [f' [H2 H3]].
    exists (- f')%f. split.
    + apply IH; auto.
    + apply derivative_on_neg; auto.
Qed.

Lemma nth_derivative_at_neg : forall n f fn' a,
  ⟦ der ^ n a ⟧ f = fn' ->
  ⟦ der ^ n a ⟧ (- f) = - fn'.
Proof.
  induction n as [| k IH]; intros f fn' a H1.
  - simpl in *. subst. lra.
  - simpl in *. destruct H1 as [d [fk [H1 [H2 H3]]]].
    exists d, (- fk)%f. split; [solve_R |].
    split.
    + apply nth_derivative_on_neg; auto.
      apply differentiable_domain_open; solve_R.
    + apply derivative_at_neg; auto.
Qed.

Lemma nth_derivative_mult_const_l : forall n c f fn',
  ⟦ der ^ n ⟧ f = fn' ->
  ⟦ der ^ n ⟧ (c * f) = (c * fn').
Proof.
  induction n as [| k IH]; intros c f fn' H1.
  - simpl in *. subst. reflexivity.
  - simpl in *. destruct H1 as [f' [H1 H2]].
    exists (c * f')%f. split.
    + apply IH; auto.
    + apply derivative_mult_const_l; auto.
Qed.

Lemma nth_derivative_on_mult_const_l : forall n c f fn' D,
  differentiable_domain D ->
  ⟦ der ^ n ⟧ f D = fn' ->
  ⟦ der ^ n ⟧ (c * f) D = (c * fn').
Proof.
  induction n as [| k IH]; intros c f fn' D H1 H2.
  - simpl in *. intros x H3. specialize (H2 x H3). rewrite H2. reflexivity.
  - simpl in *. destruct H2 as [f' [H2 H3]].
    exists (c * f')%f. split.
    + apply IH; auto.
    + apply derivative_on_mult_const_l; auto.
Qed.

Lemma nth_derivative_at_mult_const_l : forall n c f fn' a,
  ⟦ der ^ n a ⟧ f = fn' ->
  ⟦ der ^ n a ⟧ (c * f) = c * fn'.
Proof.
  induction n as [| k IH]; intros c f fn' a H1.
  - simpl in *. subst. nra.
  - simpl in *. destruct H1 as [δ [fk [H1 [H2 H3]]]].
    exists δ, (c * fk)%f. split; [solve_R |].
    split.
    + apply nth_derivative_on_mult_const_l; auto.
      apply differentiable_domain_open; solve_R.
    + apply derivative_at_mult_const_l; auto.
Qed.

Lemma nth_derivative_mult_const_r : forall n c f fn',
  ⟦ der ^ n ⟧ f = fn' ->
  ⟦ der ^ n ⟧ (fun x => f x * c) = (fun x => fn' x * c).
Proof.
  induction n as [| k IH]; intros c f fn' H1.
  - simpl in *. subst. reflexivity.
  - simpl in *. destruct H1 as [f' [H1 H2]].
    exists (fun x => f' x * c). split.
    + apply IH; auto.
    + apply derivative_mult_const_r; auto.
Qed.

Lemma nth_derivative_on_mult_const_r : forall n c f fn' D,
  differentiable_domain D ->
  ⟦ der ^ n ⟧ f D = fn' ->
  ⟦ der ^ n ⟧ (fun x => f x * c) D = (fun x => fn' x * c).
Proof.
  induction n as [| k IH]; intros c f fn' D H1 H2.
  - simpl in *. intros x H3. specialize (H2 x H3). rewrite H2. reflexivity.
  - simpl in *. destruct H2 as [f' [H2 H3]].
    exists (fun x => f' x * c). split.
    + apply IH; auto.
    + apply derivative_on_mult_const_r; auto.    
Qed.

Lemma nth_derivative_at_mult_const_r : forall n c f fn' a,
  ⟦ der ^ n a ⟧ f = fn' ->
  ⟦ der ^ n a ⟧ (fun x => f x * c) = (fun x => fn' x * c).
Proof.
  induction n as [| k IH]; intros c f fn' a H1.
  - simpl in *. subst. nra.
  - simpl in *. destruct H1 as [δ [fk [H1 [H2 H3]]]].
    exists δ, (fun x => fk x * c). split; [solve_R |].
    split.
    + apply nth_derivative_on_mult_const_r; auto.
      apply differentiable_domain_open; solve_R.
    + apply derivative_at_mult_const_r; auto.
Qed.




Lemma derivative_at_imp_derive_at : forall f f' a,
  ⟦ der a ⟧ f = f' -> ⟦ Der a ⟧ f = f' a.
Proof.
  intros f f' a H1. unfold derive, derive_at.
  assert (H2 : is_derive_limit_or_zero f a (f' a)).
  { left. unfold is_derivative_at_limit. apply H1. }
  specialize (epsilon_spec (inhabits 0) (is_derive_limit_or_zero f a)) as H3.
  assert (H4 : exists x, is_derive_limit_or_zero f a x).
  { exists (f' a). apply H2. }
  specialize (H3 H4).
  destruct H3 as [H3 | [H3 H5]].
  - unfold is_derivative_at_limit in H3. eapply limit_unique; eauto.
  - exfalso. apply H3. exists (f' a). apply H1.
Qed.

Lemma derivative_imp_derive : forall f f',
  ⟦ der ⟧ f = f' -> ⟦ Der ⟧ f = f'.
Proof.
  intros f f' H1. extensionality x. specialize (H1 x).
  apply derivative_at_imp_derive_at; auto.
Qed.

Lemma derivative_at_right_imp_derive_at_right : forall f f' a,
  ⟦ der a ⁺ ⟧ f = f' -> ⟦ Der a ⁺ ⟧ f = f' a.
Proof.
  intros f f' a H1.
  unfold derive_at_right.
  assert (H2 : is_derive_right_limit_or_zero f a (f' a)).
  { left. apply H1. }
  assert (H3 : exists x, is_derive_right_limit_or_zero f a x).
  { exists (f' a). apply H2. }
  pose proof (epsilon_spec (inhabits 0) (is_derive_right_limit_or_zero f a) H3) as H4.
  destruct H4 as [H4 | [H4 H5]].
  - apply (limit_right_unique (fun h => (f (a + h) - f a) / h) 0 _ _ H4 H1).
  - exfalso. apply H4. exists (f' a). apply H1.
Qed.

Lemma derivative_at_left_imp_derive_at_left : forall f f' a,
  ⟦ der a ⁻ ⟧ f = f' -> ⟦ Der a ⁻ ⟧ f = f' a.
Proof.
  intros f f' a H1.
  unfold derive_at_left.
  assert (H2 : is_derive_left_limit_or_zero f a (f' a)).
  { left. apply H1. }
  assert (H3 : exists x, is_derive_left_limit_or_zero f a x).
  { exists (f' a). apply H2. }
  pose proof (epsilon_spec (inhabits 0) (is_derive_left_limit_or_zero f a) H3) as H4.
  destruct H4 as [H4 | [H4 H5]].
  - apply (limit_left_unique (fun h => (f (a + h) - f a) / h) 0 _ _ H4 H1).
  - exfalso. apply H4. exists (f' a). apply H1.
Qed.

Lemma derivative_on_imp_derive_on : forall f f' D x,
  x ∈ D -> 
  ⟦ der ⟧ f D = f' -> 
  ⟦ Der ⟧ f D x = f' x.
Proof.
  intros f f' D x H1 H2.
  specialize (H2 x H1).
  unfold derive_on.
  assert (H3 : exists y, is_derive_on_limit_at_point f D x y).
  {
    destruct H2 as [[H3 H4] | [[H3 H4] | [H3 H4]]].
    - exists (f' x). left. split; auto.
      apply derivative_at_imp_derive_at in H4; auto.
    - exists (f' x). right; left. split; auto.
      apply derivative_at_right_imp_derive_at_right in H4; auto.
    - exists (f' x). right; right; left. split; auto.
      apply derivative_at_left_imp_derive_at_left in H4; auto.
  }
  pose proof (epsilon_spec (inhabits 0) (is_derive_on_limit_at_point f D x) H3) as H4.
  destruct H4 as [[H5 H6] | [[H5 H6] | [[H5 H6] | [H5 H6]]]]; auto_interval.
  - rewrite H6. destruct H2 as [[H7 H8] | [[H7 H8] | [H7 H8]]]; auto_interval.
    apply derivative_at_imp_derive_at; auto.
  - rewrite H6. destruct H2 as [[H7 H8] | [[H7 H8] | [H7 H8]]]; auto_interval.
    apply derivative_at_right_imp_derive_at_right; auto.
  - rewrite H6. destruct H2 as [[H7 H8] | [[H7 H8] | [H7 H8]]]; auto_interval.
    apply derivative_at_left_imp_derive_at_left; auto.
Qed.

Lemma derive_at_spec : forall f f' a,
  differentiable_at f a ->
  (⟦ der a ⟧ f = f' <-> ⟦ Der a ⟧ f = f' a).
Proof.
  intros f f' a H1. split.
  - apply derivative_at_imp_derive_at.
  - intros H2. destruct H1 as [L H1].
    assert (H3 : ⟦ Der a ⟧ f = L).
    { apply derivative_at_imp_derive_at with (f' := fun _ => L). unfold derivative_at. auto. }
    rewrite H2 in H3. subst L. unfold derivative_at in *. auto.
Qed.
  
Lemma derive_spec : forall f f',
  differentiable f ->
  (⟦ der ⟧ f = f' <-> ⟦ Der ⟧ f = f').
Proof.
  intros f f' H1.
  split.
  - intros H2. apply derivative_imp_derive; auto.
  - intros H2. subst f'.
    intros a. apply derive_at_spec; auto.
Qed.

Lemma derive_on_imp_derivative_on : forall f f' D,
  differentiable_on f D ->
  ⟦ Der ⟧ f D = f' -> 
  ⟦ der ⟧ f D = f'.
Proof.
  intros f f' D H1 H2.
  apply differentiable_on_imp_derivative_on in H1 as [f0 H1].
  apply derivative_on_ext with (f1' := f0).
  - intros x Hx.
    rewrite <- H2.
    symmetry.
    apply derivative_on_imp_derive_on; auto.
  - exact H1.
Qed.

Lemma derive_on_spec : forall f D,
  differentiable_on f D ->
  (⟦ der ⟧ f D = ⟦ Der ⟧ f D).
Proof.
  intros f D H.
  apply derive_on_imp_derivative_on; auto.
Qed.

Lemma derive_on_spec_at : forall f D a,
  interior_point D a ->
  differentiable_on f D ->
  (⟦ der a ⟧ f = ⟦ Der ⟧ f D).
Proof.
  intros f D a H1 H2.
  apply derivative_on_imp_derivative_at with (D := D); auto.
  apply derive_on_spec; auto.
Qed.

Lemma derive_at_eq : forall f1 f2 a,
  (exists δ, δ > 0 /\ forall x, |x - a| < δ -> f1 x = f2 x) ->
  ⟦ Der a ⟧ f1 = ⟦ Der a ⟧ f2.
Proof.
  intros f1 f2 a H1.
  destruct (classic (differentiable_at f1 a)) as [H2 | H2].
  - assert (H3 : differentiable_at f2 a).
    { eapply differentiable_at_eq; eauto. }
    destruct (differentiable_at_imp_derivative_at _ _ H2) as [f' H4].
    assert (H5 : ⟦ der a ⟧ f2 = f').
    { eapply derivative_at_eq; eauto. }
    apply derive_at_spec in H4; auto.
    apply derive_at_spec in H5; auto.
    rewrite H4, H5. reflexivity.
  - assert (H3 : ~ differentiable_at f2 a).
    { intros H3. apply H2. destruct H1 as [d [H1 H4]].
      apply differentiable_at_eq with (f1 := f2).
      exists d. split; auto. intros x H5. symmetry. apply H4; auto. auto. }
    unfold derive_at.
    assert (H4 : is_derive_limit_or_zero f1 a 0) by (right; split; auto).
    assert (H5 : exists x, is_derive_limit_or_zero f1 a x) by (exists 0; auto).
    specialize (epsilon_spec (inhabits 0) (is_derive_limit_or_zero f1 a) H5) as H6.
    destruct H6 as [H6 | [_ H6]].
    + exfalso. apply H2. exists (epsilon (inhabits 0) (is_derive_limit_or_zero f1 a)). apply H6.
    + assert (H7 : is_derive_limit_or_zero f2 a 0) by (right; split; auto).
      assert (H8 : exists x, is_derive_limit_or_zero f2 a x) by (exists 0; auto).
      specialize (epsilon_spec (inhabits 0) (is_derive_limit_or_zero f2 a) H8) as H9.
      destruct H9 as [H9 | [_ H9]].
      * exfalso. apply H3. exists (epsilon (inhabits 0) (is_derive_limit_or_zero f2 a)). apply H9.
      * rewrite H6, H9. reflexivity.
Qed.

Lemma derive_at_const : forall c a,
  ⟦ Der a ⟧ (fun _ => c) = 0.
Proof.
  intros c a. pose proof derivative_at_imp_derive_at (fun _ => c) (fun _ => 0) a as H1.
  specialize (H1 ltac:(apply derivative_at_const)). auto.
Qed.

Lemma derive_const : forall c,
  ⟦ Der ⟧ (fun _ => c) = (fun _ => 0).
Proof.
  intros c. extensionality x.
  apply derive_at_const.  
Qed.

Lemma derive_on_const : forall c D x,
  differentiable_domain D -> x ∈ D ->
  ⟦ Der ⟧ (fun _ => c) D x = 0.
Proof.
  intros c D x H1 H2.
  rewrite (derivative_on_imp_derive_on _ (fun _ => 0) D x); auto.
  apply derivative_on_const; auto.
Qed.

Lemma derive_at_id : forall a,
  ⟦ Der a ⟧ (fun x => x) = 1.
Proof.
  intros a. pose proof derivative_at_imp_derive_at (fun x => x) (fun _ => 1) a as H1.
  specialize (H1 ltac:(apply derivative_at_id)). auto.
Qed.

Lemma derive_id : 
  ⟦ Der ⟧ (fun x => x) = (fun _ => 1).
Proof.
  extensionality x.
  apply derive_at_id.  
Qed.

Lemma derive_on_id : forall D x,
  differentiable_domain D -> x ∈ D ->
  ⟦ Der ⟧ (fun x => x) D x = 1.
Proof.
  intros D x H1 H2.
  rewrite (derivative_on_imp_derive_on _ (fun _ => 1) D x); auto.
  apply derivative_on_id; auto.
Qed.

Lemma derive_at_plus : forall f g a,
  differentiable_at f a -> 
  differentiable_at g a -> 
  ⟦ Der a ⟧ (f + g) = ⟦ Der a ⟧ f + ⟦ Der a ⟧ g.
Proof.
  intros f g a H1 H2.
  apply differentiable_at_imp_derivative_at in H1 as [f' H1].
  apply differentiable_at_imp_derivative_at in H2 as [g' H2].
  rewrite (derivative_at_imp_derive_at f f' a); auto.
  rewrite (derivative_at_imp_derive_at g g' a); auto.
  rewrite (derivative_at_imp_derive_at (f + g) (f' + g') a).
  - reflexivity.
  - apply derivative_at_plus; auto.
Qed.

Lemma derive_plus : forall f g,
  differentiable f -> differentiable g ->
  ⟦ Der ⟧ (f + g) = (⟦ Der ⟧ f + ⟦ Der ⟧ g)%f.
Proof.
  intros f g H1 H2.
  apply differentiable_imp_derivative in H1 as [f' H1].
  apply differentiable_imp_derivative in H2 as [g' H2].
  rewrite (derivative_imp_derive f f'); auto.
  rewrite (derivative_imp_derive g g'); auto.
  rewrite (derivative_imp_derive (f + g) (f' + g')); auto.
  apply derivative_plus; auto.
Qed.

Lemma derive_on_plus : forall f g D x,
  differentiable_domain D ->
  x ∈ D ->
  differentiable_on f D ->
  differentiable_on g D ->
  ⟦ Der ⟧ (f + g) D x = ⟦ Der ⟧ f D x + ⟦ Der ⟧ g D x.
Proof.
  intros f g D x H1 H2 H3 H4.
  apply differentiable_on_imp_derivative_on in H3 as [f' H3].
  apply differentiable_on_imp_derivative_on in H4 as [g' H4].
  rewrite (derivative_on_imp_derive_on f f' D x H2); auto.
  rewrite (derivative_on_imp_derive_on g g' D x H2); auto.
  rewrite (derivative_on_imp_derive_on (f + g) (f' + g') D x H2); auto.
  apply derivative_on_plus; auto.
Qed.

Lemma derive_on_minus : forall f g D x,
  differentiable_domain D ->
  x ∈ D ->
  differentiable_on f D ->
  differentiable_on g D ->
  ⟦ Der ⟧ (f - g) D x = ⟦ Der ⟧ f D x - ⟦ Der ⟧ g D x.
Proof.
  intros f g D x H1 H2 H3 H4.
  apply differentiable_on_imp_derivative_on in H3 as [f' H3].
  apply differentiable_on_imp_derivative_on in H4 as [g' H4].
  rewrite (derivative_on_imp_derive_on f f' D x H2); auto.
  rewrite (derivative_on_imp_derive_on g g' D x H2); auto.
  rewrite (derivative_on_imp_derive_on (f - g) (f' - g') D x H2); auto.
  apply derivative_on_minus; auto.
Qed.

Lemma derive_minus : forall f g,
  differentiable f -> differentiable g ->
  ⟦ Der ⟧ (f - g) = (⟦ Der ⟧ f - ⟦ Der ⟧ g)%f.
Proof.
  intros f g H1 H2.
  apply differentiable_imp_derivative in H1 as [f' H1].
  apply differentiable_imp_derivative in H2 as [g' H2].
  rewrite (derivative_imp_derive f f'); auto.
  rewrite (derivative_imp_derive g g'); auto.
  rewrite (derivative_imp_derive (f - g) (f' - g')); auto.
  apply derivative_minus; auto.
Qed.

Lemma derive_at_minus : forall f g a,
  differentiable_at f a -> 
  differentiable_at g a -> 
  ⟦ Der a ⟧ (f - g) = ⟦ Der a ⟧ f - ⟦ Der a ⟧ g.
Proof.
  intros f g a H1 H2.
  apply differentiable_at_imp_derivative_at in H1 as [f' H1].
  apply differentiable_at_imp_derivative_at in H2 as [g' H2].
  rewrite (derivative_at_imp_derive_at f f' a); auto.
  rewrite (derivative_at_imp_derive_at g g' a); auto.
  rewrite (derivative_at_imp_derive_at (f - g) (f' - g') a).
  - reflexivity.
  - apply derivative_at_minus; auto.
Qed.

Lemma derive_at_mult_const_l : forall c f a,
  differentiable_at f a ->
  ⟦ Der a ⟧ (c * f) = c * ⟦ Der a ⟧ f.
Proof.
  intros c f a H1.
  apply differentiable_at_imp_derivative_at in H1 as [f' H1].
  rewrite (derivative_at_imp_derive_at f f' a); auto.
  rewrite (derivative_at_imp_derive_at (c * f) (c * f') a).
  - lra.
  - apply derivative_at_mult_const_l; auto.
Qed.

Lemma derive_mult_const_l : forall c f,
  differentiable f ->
  ⟦ Der ⟧ (c * f) = (c * ⟦ Der ⟧ f)%f.
Proof.
  intros c f H1.
  apply differentiable_imp_derivative in H1 as [f' H1].
  rewrite (derivative_imp_derive f f'); auto.
  rewrite (derivative_imp_derive (c * f) (c * f')); auto.
  apply derivative_mult_const_l; auto.
Qed.

Lemma derive_on_mult_const_l : forall c f D x,
  differentiable_domain D ->
  x ∈ D ->
  differentiable_on f D ->
  ⟦ Der ⟧ (c * f) D x = c * ⟦ Der ⟧ f D x.
Proof.
  intros c f D x H1 H2 H3.
  apply differentiable_on_imp_derivative_on in H3 as [f' H3].
  rewrite (derivative_on_imp_derive_on f f' D x H2); auto.
  rewrite (derivative_on_imp_derive_on (c * f) (c * f') D x H2); auto.
  apply derivative_on_mult_const_l; auto.
Qed.

Lemma derive_at_neg : forall f a,
  differentiable_at f a ->
  ⟦ Der a ⟧ (-f) = - ⟦ Der a ⟧ f.
Proof.
  intros f a H1.
  apply differentiable_at_imp_derivative_at in H1 as [f' H1].
  rewrite (derivative_at_imp_derive_at f f' a); auto.
  rewrite (derivative_at_imp_derive_at (-f) (-f') a).
  - reflexivity.
  - apply derivative_at_neg; auto.
Qed.

Lemma derive_neg : forall f,
  differentiable f ->
  ⟦ Der ⟧ (-f) = (- ⟦ Der ⟧ f)%f.
Proof.
  intros f H1.
  apply differentiable_imp_derivative in H1 as [f' H1].
  rewrite (derivative_imp_derive f f'); auto.
  rewrite (derivative_imp_derive (-f) (-f') ); auto.
  apply derivative_neg; auto.
Qed.

Lemma derive_on_neg : forall f D x,
  differentiable_domain D ->
  x ∈ D ->
  differentiable_on f D ->
  ⟦ Der ⟧ (-f) D x = - ⟦ Der ⟧ f D x.
Proof.
  intros f D x H1 H2 H3.
  apply differentiable_on_imp_derivative_on in H3 as [f' H3].
  rewrite (derivative_on_imp_derive_on f f' D x H2); auto.
  rewrite (derivative_on_imp_derive_on (-f) (-f') D x H2); auto.
  apply derivative_on_neg; auto.
Qed.

Lemma derive_at_mult_const_r : forall f c a,
  differentiable_at f a ->
  ⟦ Der a ⟧ (fun x => f x * c) = ⟦ Der a ⟧ f * c.
Proof.
  intros f c a H1.
  apply differentiable_at_imp_derivative_at in H1 as [f' H1].
  rewrite (derivative_at_imp_derive_at f f' a); auto.
  rewrite (derivative_at_imp_derive_at (fun x => f x * c) (fun x => f' x * c) a).
  - reflexivity.
  - apply derivative_at_mult_const_r; auto.
Qed.

Lemma derive_mult_const_r : forall f c,
  differentiable f ->
  ⟦ Der ⟧ (fun x => f x * c) = (fun x => (⟦ Der ⟧ f) x * c).
Proof.
  intros f c H1.
  apply differentiable_imp_derivative in H1 as [f' H1].
  rewrite (derivative_imp_derive f f'); auto.
  rewrite (derivative_imp_derive (fun x => f x * c) (fun x => f' x * c)); auto.
  apply derivative_mult_const_r; auto.
Qed.

Lemma derive_on_mult_const_r : forall f c D x,
  differentiable_domain D ->
  x ∈ D ->
  differentiable_on f D ->
  ⟦ Der ⟧ (fun x => f x * c) D x = ⟦ Der ⟧ f D x * c.
Proof.
  intros f c D x H1 H2 H3.
  apply differentiable_on_imp_derivative_on in H3 as [f' H3].
  rewrite (derivative_on_imp_derive_on f f' D x H2); auto.
  rewrite (derivative_on_imp_derive_on (fun x => f x * c) (fun x => f' x * c) D x H2); auto.
  apply derivative_on_mult_const_r; auto.
Qed.

Lemma derive_at_mult : forall f g a,
  differentiable_at f a ->
  differentiable_at g a ->
  ⟦ Der a ⟧ (f ∙ g) = ⟦ Der a ⟧ f * g a + f a * ⟦ Der a ⟧ g.
Proof.
  intros f g a H1 H2.
  apply differentiable_at_imp_derivative_at in H1 as [f' H1].
  apply differentiable_at_imp_derivative_at in H2 as [g' H2].
  rewrite (derivative_at_imp_derive_at f f' a); auto.
  rewrite (derivative_at_imp_derive_at g g' a); auto.
  rewrite (derivative_at_imp_derive_at (f ∙ g) (f' ∙ g + f ∙ g')%f a).
  - reflexivity.
  - apply derivative_at_mult; auto.
Qed.

Lemma derive_mult : forall f g,
  differentiable f ->
  differentiable g ->
  ⟦ Der ⟧ (f ∙ g) = (⟦ Der ⟧ f ∙ g + f ∙ ⟦ Der ⟧ g)%f.
Proof.
  intros f g H1 H2.
  apply differentiable_imp_derivative in H1 as [f' H1].
  apply differentiable_imp_derivative in H2 as [g' H2].
  rewrite (derivative_imp_derive f f'); auto.
  rewrite (derivative_imp_derive g g'); auto.
  rewrite (derivative_imp_derive (f ∙ g) (f' ∙ g + f ∙ g')%f); auto.
  apply derivative_mult; auto.
Qed.

Lemma derive_on_mult : forall f g D x,
  differentiable_domain D ->
  x ∈ D ->
  differentiable_on f D ->
  differentiable_on g D ->
  ⟦ Der ⟧ (f ∙ g) D x = ⟦ Der ⟧ f D x * g x + f x * ⟦ Der ⟧ g D x.
Proof.
  intros f g D x H1 H2 H3 H4.
  apply differentiable_on_imp_derivative_on in H3 as [f' H3].
  apply differentiable_on_imp_derivative_on in H4 as [g' H4].
  rewrite (derivative_on_imp_derive_on f f' D x H2); auto.
  rewrite (derivative_on_imp_derive_on g g' D x H2); auto.
  rewrite (derivative_on_imp_derive_on (f ∙ g) (f' ∙ g + f ∙ g')%f D x H2); auto.
  apply derivative_on_mult; auto.
Qed.

Lemma derive_at_inv : forall f a,
  differentiable_at f a ->
  f a <> 0 ->
  ⟦ Der a ⟧ (fun x => / f x) = - ⟦ Der a ⟧ (fun x => f x / (f a)^2).
Proof.
  intros f a H1 H2.
  apply differentiable_at_imp_derivative_at in H1 as [f' H1].
  rewrite (derivative_at_imp_derive_at (fun x => / f x) (λ x, -1 * f' x / f x ^ 2) a); [| apply derivative_at_inv; auto].
  rewrite (derivative_at_imp_derive_at (λ x, f x / (f a)^2) (λ x, f' x / (f a)^2) a).
  - lra.
  - apply derivative_at_mult_const_r; auto.
Qed.

Lemma derive_inv : forall f,
  differentiable f ->
  (forall x, f x <> 0) ->
  ⟦ Der ⟧ (fun x => / f x) = (fun x => - (⟦ Der ⟧ f) x / (f x)^2).
Proof.
  intros f H1 H2. extensionality x.
  rewrite derive_at_inv; auto.
  replace (λ y, f y / (f x)^2) with (λ y, f y * (1 / (f x)^2)); [| extensionality y; field; auto].
  rewrite derive_at_mult_const_r; auto. solve_R.
Qed.

Lemma derive_on_inv : forall f D x,
  differentiable_domain D ->
  x ∈ D ->
  differentiable_on f D ->
  (forall y, y ∈ D -> f y <> 0) ->
  ⟦ Der ⟧ (fun y => / f y) D x = - ⟦ Der ⟧ f D x / (f x)^2.
Proof.
  intros f D x H1 H2 H3 H4.
  apply differentiable_on_imp_derivative_on in H3 as [f' H3].
  rewrite (derivative_on_imp_derive_on f f' D x H2); auto.
  rewrite (derivative_on_imp_derive_on (fun y => / f y) (fun y => -1 * f' y / (f y)^2) D x H2).
  - lra.
  - apply derivative_on_inv; auto.
Qed.

Lemma derive_at_div : forall f g a,
  differentiable_at f a ->
  differentiable_at g a ->
  g a <> 0 ->
  ⟦ Der a ⟧ (fun x => f x / g x) = (⟦ Der a ⟧ f * g a - f a * ⟦ Der a ⟧ g) / (g a)^2.
Proof.
  intros f g a H1 H2 H3.
  apply differentiable_at_imp_derivative_at in H1 as [f' H1].
  apply differentiable_at_imp_derivative_at in H2 as [g' H2].
  rewrite (derivative_at_imp_derive_at f f' a); auto.
  rewrite (derivative_at_imp_derive_at g g' a); auto.
  rewrite (derivative_at_imp_derive_at (fun x => f x / g x) (λ x, (f' x * g x -  g' x * f x) / (g x * g x)) a).
  - simpl. solve_R.
  - apply derivative_at_div; auto.
Qed.

Lemma derive_div : forall f g,
  differentiable f ->
  differentiable g ->
  (forall x, g x <> 0) ->
  ⟦ Der ⟧ (f / g) = (λ x, ((⟦ Der ⟧ f) x * g x - f x * (⟦ Der ⟧ g) x) / (g x)^2).
Proof.
  intros f g H1 H2 H3.
  extensionality x.
  rewrite derive_at_div; auto.
Qed.

Lemma derive_on_div : forall f g D x,
  differentiable_domain D ->
  x ∈ D ->
  differentiable_on f D ->
  differentiable_on g D ->
  (forall y, y ∈ D -> g y <> 0) ->
  ⟦ Der ⟧ (f / g) D x = (⟦ Der ⟧ f D x * g x - f x * ⟦ Der ⟧ g D x) / (g x)^2.
Proof.
  intros f g D x H1 H2 H3 H4 H5.
  apply differentiable_on_imp_derivative_on in H3 as [f' H3].
  apply differentiable_on_imp_derivative_on in H4 as [g' H4].
  rewrite (derivative_on_imp_derive_on f f' D x H2); auto.
  rewrite (derivative_on_imp_derive_on g g' D x H2); auto.
  rewrite (derivative_on_imp_derive_on (f / g) (λ x, (f' x * g x - g' x * f x) / (g x * g x)) D x H2).
  - solve_R.
  - apply derivative_on_div; auto.
Qed.

Lemma derive_at_comp : forall f g a,
  differentiable_at f a ->
  differentiable_at g (f a) ->
  ⟦ Der a ⟧ (g ∘ f) = ⟦ Der (f a) ⟧ g * ⟦ Der a ⟧ f.
Proof.
  intros f g a H1 H2.
  apply differentiable_at_imp_derivative_at in H1 as [f' H1].
  apply differentiable_at_imp_derivative_at in H2 as [g' H2].
  rewrite (derivative_at_imp_derive_at f f' a); auto.
  rewrite (derivative_at_imp_derive_at g g' (f a)); auto.
  rewrite (derivative_at_imp_derive_at (g ∘ f) ((g' ∘ f) ∙ f')%f a).
  - reflexivity.
  - apply derivative_at_comp; auto.
Qed.

Lemma derive_comp : forall f g,
  differentiable f ->
  differentiable g ->
  ⟦ Der ⟧ (g ∘ f) = ((⟦ Der ⟧ g ∘ f) ∙ ⟦ Der ⟧ f)%f.
Proof.
  intros f g H1 H2.
  extensionality x.
  rewrite derive_at_comp; auto.
Qed.

Lemma derive_at_sqrt : forall a,
  a > 0 ->
  ⟦ Der a ⟧ sqrt = 1 / (2 * sqrt a).
Proof.
  intros a H1.
  rewrite (derivative_at_imp_derive_at sqrt (λ x, 1 / (2 * sqrt x)) a).
  - reflexivity.
  - apply derivative_at_sqrt; auto.
Qed.

Lemma derive_sqrt : forall x,
  x > 0 ->
  (⟦ Der ⟧ sqrt) x = 1 / (2 * sqrt x).
Proof.
  intros x H1.
  rewrite derive_at_sqrt; auto.
Qed.

Lemma derive_on_sqrt : forall D x,
  differentiable_domain D ->
  x ∈ D ->
  (forall y, y ∈ D -> y > 0) ->
  ⟦ Der ⟧ sqrt D x = 1 / (2 * sqrt x).
Proof.
  intros D x H1 H2 H3.
  rewrite (derivative_on_imp_derive_on sqrt (λ y, 1 / (2 * sqrt y)) D x H2).
  - reflexivity.
  - apply derivative_on_sqrt; auto.
Qed.

Lemma derive_at_sqrt_comp : forall f a,
  differentiable_at f a ->
  f a > 0 ->
  ⟦ Der a ⟧ (fun x => sqrt (f x)) = ⟦ Der a ⟧ f / (2 * sqrt (f a)).
Proof.
  intros f a H1 H2.
  apply differentiable_at_imp_derivative_at in H1 as [f' H1].
  rewrite (derivative_at_imp_derive_at f f' a); auto.
  rewrite (derivative_at_imp_derive_at (fun x => sqrt (f x)) (fun x => f' x / (2 * sqrt (f x))) a).
  - reflexivity.
  - apply derivative_at_sqrt_comp; auto.
Qed.

Lemma derive_sqrt_comp : forall f,
  differentiable f ->
  (forall x, f x > 0) ->
  ⟦ Der ⟧ (fun x => sqrt (f x)) = (fun x => (⟦ Der ⟧ f) x / (2 * sqrt (f x))).
Proof.
  intros f H1 H2.
  apply differentiable_imp_derivative in H1 as [f' H1].
  rewrite (derivative_imp_derive f f'); auto.
  rewrite (derivative_imp_derive (fun x => sqrt (f x)) (fun x => f' x / (2 * sqrt (f x)))); auto.
  apply derivative_sqrt_comp; auto.
Qed.

Lemma derive_on_sqrt_comp : forall f D x,
  differentiable_domain D ->
  x ∈ D ->
  differentiable_on f D ->
  (forall y, y ∈ D -> f y > 0) ->
  ⟦ Der ⟧ (fun x => sqrt (f x)) D x = ⟦ Der ⟧ f D x / (2 * sqrt (f x)).
Proof.
  intros f D x H1 H2 H3 H4.
  apply differentiable_on_imp_derivative_on in H3 as [f' H3].
  rewrite (derivative_on_imp_derive_on f f' D x H2); auto.
  rewrite (derivative_on_imp_derive_on (fun x => sqrt (f x)) (fun x => f' x / (2 * sqrt (f x))) D x H2); auto.
  apply derivative_on_sqrt_comp; auto.
Qed.

Lemma derive_at_sum : forall (f : nat -> R -> R) n i a,
  (i <= n)%nat ->
  (forall k, (i <= k <= n)%nat -> differentiable_at (f k) a) ->
  ⟦ Der a ⟧ (fun x => ∑ i n (fun k => f k x)) = ∑ i n (fun k => ⟦ Der a ⟧ (f k)).
Proof.
  intros f n i a H1 H2.
  apply derivative_at_imp_derive_at with (f' := fun x => ∑ i n (fun k => ⟦ Der a ⟧ (f k))).
  apply derivative_at_sum with (f' := fun k x => ⟦ Der a ⟧ (f k)); auto.
  intros k H3. apply derive_at_spec; auto.
Qed.

Lemma derive_sum : forall (f : nat -> R -> R) n i,
  (i <= n)%nat ->
  (forall k, (i <= k <= n)%nat -> differentiable (f k)) ->
  ⟦ Der ⟧ (fun x => ∑ i n (fun k => f k x)) = (fun x => ∑ i n (fun k => (⟦ Der ⟧ (f k)) x)).
Proof.
  intros f n i H1 H2.
  extensionality x.
  apply derive_at_sum; auto.
  intros k H3. apply H2; auto.
Qed.

Lemma derive_on_sum : forall (f : nat -> R -> R) D n i x,
  differentiable_domain D ->
  (i <= n)%nat ->
  x ∈ D ->
  (forall k, (i <= k <= n)%nat -> differentiable_on (f k) D) ->
  ⟦ Der ⟧ (fun x => ∑ i n (fun k => f k x)) D x = ∑ i n (fun k => ⟦ Der ⟧ (f k) D x).
Proof.
  intros f D n i x H1 H2 H3 H4.
  set (f' := fun k => ⟦ Der ⟧ (f k) D).
  rewrite derivative_on_imp_derive_on with (f' := fun y => ∑ i n (fun k => f' k y)); auto.
  apply derivative_on_sum with (f' := f'); auto.
  intros k H5. unfold f'.
  pose proof (differentiable_on_imp_derivative_on (f k) D (H4 k H5)) as [g H6].
  eapply derivative_on_ext with (f1' := g); auto.
  intros y H7. symmetry.
  apply derivative_on_imp_derive_on with (f' := g); auto.
Qed.

Lemma nth_derive_0 : forall f,
  ⟦ Der ^ 0 ⟧ f = f.
Proof.
  intros f. simpl. reflexivity.
Qed.

Lemma nth_derive_at_0 : forall f a,
  ⟦ Der ^ 0 a ⟧ f = f a.
Proof.
  intros f a. simpl. reflexivity.
Qed.

Lemma nth_derive_1 : forall f,
  ⟦ Der ^ 1 ⟧ f = ⟦ Der ⟧ f.
Proof.
  intros f. simpl. reflexivity.
Qed.

Lemma nth_derive_at_1 : forall f a,
  ⟦ Der ^ 1 a ⟧ f = ⟦ Der a ⟧ f.
Proof.
  intros f a. simpl. reflexivity.
Qed.

Lemma nth_derive_succ : forall n f,
  ⟦ Der ^ (S n) ⟧ f = ⟦ Der ^ n ⟧ (⟦ Der ⟧ f).
Proof.
  induction n as [| k IH]; intros f.
  - reflexivity.
  - simpl. rewrite <- IH. reflexivity.
Qed.

Lemma nth_derive_at_succ : forall n f a,
  ⟦ Der ^ (S n) a ⟧ f = ⟦ Der ^ n a ⟧ (⟦ Der ⟧ f).
Proof.
  intros n f a.
  rewrite <- nth_derive_succ.
  reflexivity.
Qed.

Lemma nth_derive_comm : forall n f,
  ⟦ Der ⟧ (⟦ Der ^ n ⟧ f) = ⟦ Der ^ n ⟧ (⟦ Der ⟧ f).
Proof.
  induction n as [| k IH]; intros f.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma nth_derive_at_comm : forall n f a,
  ⟦ Der a ⟧ (⟦ Der ^ n ⟧ f) = ⟦ Der ^ n a ⟧ (⟦ Der ⟧ f).
Proof.
  intros n f a.
  rewrite <- nth_derive_comm.
  reflexivity.
Qed.

Lemma nth_derive_on_comm : forall n f D,
  ⟦ Der ⟧ (⟦ Der ^ n ⟧ f D) D = ⟦ Der ^ n ⟧ (⟦ Der ⟧ f D) D.
Proof.
  induction n as [| k IH]; intros f D.
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma nth_derive_on_succ : forall n f D,
  ⟦ Der ^ (S n) ⟧ f D = ⟦ Der ^ n ⟧ (⟦ Der ⟧ f D) D.
Proof.
  induction n as [| k IH]; intros f D.
  - reflexivity.
  - simpl. rewrite <- IH. reflexivity.
Qed.

Lemma nth_derivative_imp_nth_derive : forall n f f',
  ⟦ der ^ n ⟧ f = f' -> ⟦ Der ^ n ⟧ f = f'.
Proof.
  induction n as [| k IH]; intros f f' H1; simpl in H1.
  - subst. reflexivity.
  - destruct H1 as [f1' [H1 H2]]. simpl. rewrite IH with (f' := f1'); auto.
    apply derivative_imp_derive in H2; auto.
Qed.

Lemma nth_derive_at_eq : forall n f g a δ,
  δ > 0 ->
  (forall x, |x - a| < δ -> f x = g x) ->
  (⟦ Der ^ n a ⟧ f) = ⟦ Der ^ n a ⟧ g.
Proof.
  induction n as [| k IH]; intros f g a δ H1 H2.
  - simpl. apply H2. solve_R.
  - repeat rewrite nth_derive_at_succ.
    rewrite <- nth_derive_at_comm.
    specialize (IH (⟦ Der ⟧ f) (⟦ Der ⟧ g) a (δ/2) ltac:(solve_R)). rewrite <- IH.
    2 : {
      intros x H3. apply derive_at_eq. exists (δ/2). split; try solve [solve_R].
      intros y H4. specialize (H2 y ltac:(solve_R)). auto.
    }
    rewrite nth_derive_at_comm. auto.
Qed.

Lemma nth_derivative_on_open_imp_nth_derive_eq : forall n f fn D,
  (forall x, x ∈ D -> interior_point D x) -> (* Assumption: D is open *)
  ⟦ der ^ n ⟧ f D = fn ->
  forall x, x ∈ D -> (⟦ Der ^ n ⟧ f) x = fn x.
Proof.
  induction n as [| k IH].
  - intros f fn D H1 H2 x H3. simpl in *. rewrite <- H2; auto.
  - intros f fn D H1 H2 x H3. simpl in *. destruct H2 as [fk [H4 H5]].
    rewrite derivative_at_imp_derive_at with (f' := fn); auto.
    apply derivative_at_eq with (f1 := fk).
    + destruct (H1 x H3) as [δ [H2 H6]]. exists δ. split; auto.
      intros y H7. specialize (IH f fk D H1 H4 y). rewrite IH; auto. apply H6; solve_R.
    + apply derivative_on_imp_derivative_at with (D := D); auto.
Qed.

Lemma nth_derivative_at_imp_nth_derive_at : forall n a f f',
  ⟦ der ^ n a ⟧ f = f' -> ⟦ Der ^ n a ⟧ f = f' a.
Proof.
  destruct n as [| k].
  - simpl. intros a f f' H1. subst. lra.
  - simpl. intros a f f' [δ [fk [H1 [H2 H3]]]].
    rewrite derive_at_eq with (f2 := fk).
    + apply derivative_at_imp_derive_at; auto.
    + exists δ. split; auto. intros x H4.
      apply nth_derivative_on_open_imp_nth_derive_eq with (D := (a - δ, a + δ)); auto.
      * intros y Hy. auto_interval.
      * auto_interval.
Qed.

Lemma derive_at_right_eq : forall f1 f2 a,
  (exists δ, δ > 0 /\ forall x, a <= x < a + δ -> f1 x = f2 x) ->
  ⟦ Der a ⁺ ⟧ f1 = ⟦ Der a ⁺ ⟧ f2.
Proof.
  intros f1 f2 a [δ [H1 H2]].
  destruct (classic (differentiable_at_right f1 a)) as [H3 | H3].
  - assert (H4 : differentiable_at_right f2 a).
    { eapply differentiable_at_right_eq; eauto. }
    destruct (differentiable_at_right_imp_derivative_at_right _ _ H3) as [f1' H5].
    destruct (differentiable_at_right_imp_derivative_at_right _ _ H4) as [f2' H6].
    assert (H7 : f1' a = f2' a).
    {
      eapply derivative_at_right_unique with (f := f1); eauto.
      eapply derivative_at_right_eq with (f1 := f2); eauto.
      exists δ; split; auto. intros x H7. rewrite H2; auto.
    }
    rewrite (derivative_at_right_imp_derive_at_right _ _ _ H5).
    rewrite (derivative_at_right_imp_derive_at_right _ _ _ H6).
    auto.
  - assert (H4 : ~ differentiable_at_right f2 a).
    { intros H4. apply H3. apply differentiable_at_right_eq with (f1 := f2); auto. exists δ; split; auto. intros x H5. rewrite H2; auto. }
    unfold derive_at_right.
    assert (H5 : is_derive_right_limit_or_zero f1 a 0) by (right; split; auto).
    assert (H6 : exists x, is_derive_right_limit_or_zero f1 a x) by (exists 0; auto).
    specialize (epsilon_spec (inhabits 0) (is_derive_right_limit_or_zero f1 a) H6) as H7.
    destruct H7 as [H7 | [_ H7]].
    + exfalso. apply H3. exists (epsilon (inhabits 0) (is_derive_right_limit_or_zero f1 a)). apply H7.
    + assert (H8 : is_derive_right_limit_or_zero f2 a 0) by (right; split; auto).
      assert (H9 : exists x, is_derive_right_limit_or_zero f2 a x) by (exists 0; auto).
      specialize (epsilon_spec (inhabits 0) (is_derive_right_limit_or_zero f2 a) H9) as H10.
      destruct H10 as [H10 | [_ H10]].
      * exfalso. apply H4. exists (epsilon (inhabits 0) (is_derive_right_limit_or_zero f2 a)). apply H10.
      * rewrite H7, H10. reflexivity.
Qed.

Lemma derive_at_left_eq : forall f1 f2 a,
  (exists δ, δ > 0 /\ forall x, a - δ < x <= a -> f1 x = f2 x) ->
  ⟦ Der a ⁻ ⟧ f1 = ⟦ Der a ⁻ ⟧ f2.
Proof.
  intros f1 f2 a [δ [H1 H2]].
  destruct (classic (differentiable_at_left f1 a)) as [H3 | H3].
  - assert (H4 : differentiable_at_left f2 a).
    { eapply differentiable_at_left_eq; eauto. }
    destruct (differentiable_at_left_imp_derivative_at_left _ _ H3) as [f1' H5].
    destruct (differentiable_at_left_imp_derivative_at_left _ _ H4) as [f2' H6].
    assert (H7 : f1' a = f2' a).
    {
      eapply derivative_at_left_unique with (f := f1); eauto.
      eapply derivative_at_left_eq with (f1 := f2); eauto.
      exists δ; split; auto. intros x H7. rewrite H2; auto.
    }
    rewrite (derivative_at_left_imp_derive_at_left _ _ _ H5).
    rewrite (derivative_at_left_imp_derive_at_left _ _ _ H6).
    auto.
  - assert (H4 : ~ differentiable_at_left f2 a).
    { intros H4. apply H3. apply differentiable_at_left_eq with (f1 := f2); auto. exists δ; split; auto. intros x H5. rewrite H2; auto. }
    unfold derive_at_left.
    assert (H5 : is_derive_left_limit_or_zero f1 a 0) by (right; split; auto).
    assert (H6 : exists x, is_derive_left_limit_or_zero f1 a x) by (exists 0; auto).
    specialize (epsilon_spec (inhabits 0) (is_derive_left_limit_or_zero f1 a) H6) as H7.
    destruct H7 as [H7 | [_ H7]].
    + exfalso. apply H3. exists (epsilon (inhabits 0) (is_derive_left_limit_or_zero f1 a)). apply H7.
    + assert (H8 : is_derive_left_limit_or_zero f2 a 0) by (right; split; auto).
      assert (H9 : exists x, is_derive_left_limit_or_zero f2 a x) by (exists 0; auto).
      specialize (epsilon_spec (inhabits 0) (is_derive_left_limit_or_zero f2 a) H9) as H10.
      destruct H10 as [H10 | [_ H10]].
      * exfalso. apply H4. exists (epsilon (inhabits 0) (is_derive_left_limit_or_zero f2 a)). apply H10.
      * rewrite H7, H10. reflexivity.
Qed.

Lemma derive_on_eq : forall f g D x,
  differentiable_domain D ->
  (forall y, y ∈ D -> f y = g y) ->
  x ∈ D ->
  ⟦ Der ⟧ f D x = ⟦ Der ⟧ g D x.
Proof.
  intros f g D x H1 H2 H3.
  unfold derive_on.
  assert (H4 : is_derive_on_limit_at_point f D x = is_derive_on_limit_at_point g D x).
  {
    extensionality y. apply propositional_extensionality.
    assert (H4 : interior_point D x -> ⟦ Der x ⟧ f = ⟦ Der x ⟧ g).
    {
      intros H4. apply derive_at_eq. destruct H4 as [δ [H4 H5]].
      exists δ. split; auto. intros z H6. apply H2. apply H5. solve_R.
    }
    assert (H5 : left_endpoint D x -> ⟦ Der x ⁺ ⟧ f = ⟦ Der x ⁺ ⟧ g).
    {
      intros H5. apply derive_at_right_eq. destruct H5 as [δ [H5 H6]].
      exists δ. split; auto. intros z H7. apply H2. apply H6. auto_interval.
    }
    assert (H6 : right_endpoint D x -> ⟦ Der x ⁻ ⟧ f = ⟦ Der x ⁻ ⟧ g).
    {
      intros H6. apply derive_at_left_eq. destruct H6 as [δ [H6 H7]].
      exists δ. split; auto. intros z H8. apply H2. apply H7. auto_interval.
    }
    split; intros [H7 | [H7 | [H7 | H7]]].
    - left. destruct H7 as [H7 H8]. split; auto. rewrite <- H4; auto.
    - right; left. destruct H7 as [H7 H8]. split; auto. rewrite <- H5; auto.
    - right; right; left. destruct H7 as [H7 H8]. split; auto. rewrite <- H6; auto.
    - right; right; right. auto.
    - left. destruct H7 as [H7 H8]. split; auto. rewrite H4; auto.
    - right; left. destruct H7 as [H7 H8]. split; auto. rewrite H5; auto.
    - right; right; left. destruct H7 as [H7 H8]. split; auto. rewrite H6; auto.
    - right; right; right. auto.
  }
  rewrite H4. reflexivity.
Qed.

Lemma nth_derivative_on_imp_nth_derive_on : forall n f f' D,
  differentiable_domain D ->
  ⟦ der ^ n ⟧ f D = f' -> 
  (forall x, x ∈ D -> ⟦ Der ^ n ⟧ f D x = f' x).
Proof.
  induction n as [| k IH].
  - intros f f' D H1 H2 x H3. simpl in *. apply H2; auto.
  - intros f f' D H1 H2 x H3. simpl in *. destruct H2 as [fk [H2 H4]].
    rewrite derivative_on_imp_derive_on with (f' := f'); auto.
    apply derivative_on_eq with (f1 := fk).
    + intros y Hy. symmetry. apply IH; auto.
    + apply H4.
Qed.

Lemma nth_derive_spec : forall n f,
  nth_differentiable n f ->
  ⟦ der ^ n ⟧ f = ⟦ Der ^ n ⟧ f.
Proof.
  intros n f [f' H1].
  apply nth_derivative_imp_nth_derive in H1 as H2.
  rewrite H2; auto.
Qed.

Lemma nth_derive_at_spec : forall n f a,
  nth_differentiable_at n f a ->
  ⟦ der ^ n a ⟧ f = ⟦ Der ^ n ⟧ f.
Proof.
  intros n f a [f' H1].
  pose proof (nth_derivative_at_imp_nth_derive_at n a f f' H1) as H2.
  destruct n as [| k].
  - simpl in *. rewrite H2. auto.
  - simpl in *. destruct H1 as [δ [fk [H1 [H3 H4]]]].
    exists δ, fk. split; [auto | split; auto].
    unfold derivative_at in *. rewrite <- H2 in H4. auto.
Qed.

Lemma nth_derive_add : forall n m f,
  ⟦ Der ^ n ⟧ (⟦ Der ^ m ⟧ f) = ⟦ Der ^ (n + m) ⟧ f.
Proof.
  intros n m f. induction n as [| k IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma nth_derivative_pow : forall n k, (k <= n)%nat ->
  ⟦ der ^ k ⟧ (fun x => x ^ n) = (fun x => (n! / (n-k)!) * x ^ (n - k)).
Proof.
  induction n as [| n IH].
  - intros n H1. replace n with 0%nat by lia. simpl. extensionality x. lra.
  - intros k H1. destruct k as [| p].
    + simpl. extensionality x. assert (n = 0 \/ n > 0)%nat as [H2 | H2] by lia.
      * subst n. simpl. lra.
      * assert (H3 : n! > 0) by (pose proof INR_fact_lt_0 n; lra). solve_R.
    + apply nth_derivative_succ_iff. exists (fun x => INR (S n) * x ^ n). split.
      * replace (λ x : ℝ, S n * x ^ n) with (λ x : ℝ, S n * x ^ (S n - 1)).
        2 : { extensionality y. replace (S n - 1)%nat with n by lia. reflexivity. }
        apply derivative_pow.
      * replace (λ x : ℝ, (S n)! / (S n - S p)! * x ^ (S n - S p)) with (λ x : ℝ, (S n) * (n ! / (S n - S p)! * x ^ (S n - S p))).
        2 : { extensionality x. assert (n = 0 \/ n > 0)%nat as [H2 | H2] by lia. rewrite H2. simpl. lra. rewrite fact_simpl. solve_R. apply INR_fact_neq_0. }
        apply nth_derivative_mult_const_l; auto. apply IH; lia.
Qed.

Lemma nth_derivative_at_pow : forall n k a,
  (k <= n)%nat ->
  ⟦ der ^ k a ⟧ (fun x => x ^ n) = (fun x => (n! / (n-k)!) * a ^ (n - k)).
Proof.
  intros n k a H1.
  pose proof (nth_derivative_pow n k H1) as H2.
  destruct k as [| p].
  - simpl in *. rewrite Nat.sub_0_r. solve_R. apply INR_fact_neq_0.
  - simpl in *. destruct H2 as [x [H2 H3]].
    exists 1, x. split; [lra |]. split.
    + apply nth_derivative_imp_nth_derivative_on.
      * apply differentiable_domain_open; lra.
      * exact H2.
    + unfold derivative_at. specialize (H3 a). auto.
Qed.

Lemma nth_derivative_on_pow : forall n k D,
  differentiable_domain D ->
  (k <= n)%nat ->
  ⟦ der ^ k ⟧ (fun x => x ^ n) D = (fun x => (n! / (n-k)!) * x ^ (n - k)).
Proof.
  intros n k D H1 H2.
  pose proof (nth_derivative_pow n k H2) as H3.
  apply nth_derivative_imp_nth_derivative_on; auto.
Qed.

Lemma nth_derivative_const : forall n c,
  (n > 0)%nat -> ⟦ der ^ n ⟧ (λ _, c) = (λ x, 0).
Proof.
  intros n c. generalize dependent c. induction n as [| k IH]; try lia.
  - intros c H1. assert ((k = 0)%nat \/ (k > 0)%nat) as [H2 | H2] by lia.
    -- subst k. exists (λ x, c). split.
       ++ simpl. reflexivity.
       ++ apply derivative_const.
    -- specialize (IH c H2) as H3. exists (λ x, 0). split; auto.
       apply derivative_const.
Qed. 

Lemma nth_derivative_at_const : forall n c a,
  (n > 0)%nat -> ⟦ der ^ n a ⟧ (λ _, c) = (λ _, 0).
Proof.
  intros n c a H1.
  pose proof (nth_derivative_const n c H1) as H2.
  destruct n as [| p].
  - lia.
  - simpl in *. destruct H2 as [x [H2 H3]].
    exists 1, x. split; [lra |]. split.
    + apply nth_derivative_imp_nth_derivative_on.
      * apply differentiable_domain_open; lra.
      * exact H2.
    + unfold derivative_at. specialize (H3 a). auto.
Qed.

Lemma nth_derivative_on_const : forall n c D,
  differentiable_domain D ->
  (n > 0)%nat -> ⟦ der ^ n ⟧ (λ _, c) D = (λ x, 0).
Proof.
  intros n c D H1 H2.
  pose proof (nth_derivative_const n c H2) as H3.
  apply nth_derivative_imp_nth_derivative_on; auto.
Qed.

Lemma nth_derivative_pow_gt : forall k n, (k > n)%nat ->
  ⟦ der ^ k ⟧ (fun x => x ^ n) = (fun x => 0).
Proof.
  induction k as [| k IH]; intros n H1; try lia.

  simpl. assert (n = 0 \/ n > 0)%nat as [H2 | H2]; assert (k = 0 \/ k > 0)%nat as [H3 | H3]; try lia; subst.
  - exists (fun x => 1). split. 
    + replace (λ x : ℝ, x ^ 0) with (λ x : ℝ, 1). 2 : { extensionality x. rewrite pow_O. auto. }
      reflexivity.
    + apply derivative_const.
  - exists (fun x => 0). split; try reflexivity.
    + replace (λ x : ℝ, x ^ 0) with (λ x : ℝ, 1). 2 : { extensionality x. rewrite pow_O. auto. }
      apply nth_derivative_const; lia.
    + apply derivative_const.
  - assert ((k = n)%nat \/ (k > n)%nat) as [H4 | H4]; try lia.
    + subst. exists (λ _, INR (fact n)). split.
      * pose proof (nth_derivative_pow n n ltac:(lia)) as H5. replace (λ x : ℝ, n! / (n - n)! * x ^ (n - n)) with (λ x : ℝ, INR (n !)) in H5.
        2 : { extensionality x. rewrite Nat.sub_diag, pow_O. simpl. lra. } auto.
      * apply derivative_const.
    + specialize (IH n H4).
      exists (λ _, 0). split; auto. apply derivative_const.
Qed.

Lemma nth_derivative_at_pow_gt : forall k n a,
  (k > n)%nat ->
  ⟦ der ^ k a ⟧ (fun x => x ^ n) = (fun x => 0).
Proof.
  intros k n a H1.
  pose proof (nth_derivative_pow_gt k n H1) as H2.
  destruct k as [| p].
  - lia.
  - simpl in *. destruct H2 as [x [H2 H3]].
    exists 1, x. split; [lra |]. split.
    + apply nth_derivative_imp_nth_derivative_on.
      * apply differentiable_domain_open; lra.
      * exact H2.
    + unfold derivative_at. specialize (H3 a). auto.
Qed.

Lemma nth_derivative_on_pow_gt : forall k n D,
  differentiable_domain D ->
  (k > n)%nat ->
  ⟦ der ^ k ⟧ (fun x => x ^ n) D = (fun x => 0).
Proof.
  intros k n D H1 H2.
  pose proof (nth_derivative_pow_gt k n H2) as H3.
  apply nth_derivative_imp_nth_derivative_on; auto.
Qed.

Lemma nth_derivative_at_zero_pow : forall n k,
  ⟦ der^k 0 ⟧ (fun x => x ^ n) = (fun _ => if Nat.eq_dec n k then INR (fact k) else 0).
Proof.
  intros n k. assert ((n = k)%nat \/ (n < k)%nat \/ (n > k)%nat) as [H1 | [H1 | H1]] by lia.
  - rewrite H1. replace (λ _ : ℝ, if Nat.eq_dec k k then INR (k!) else 0) with (λ _ : ℝ, INR (fact k)).
    2 : { extensionality x. simpl. destruct (Nat.eq_dec k k); try lia; lra. }
   pose proof (nth_derivative_at_pow n n 0 ltac:(lia)) as H2.
    replace (λ x : ℝ, n! / (n - n)! * 0 ^ (n - n)) with (λ x : ℝ, INR (fact n)) in H2; subst; auto.
    extensionality x. rewrite Nat.sub_diag. simpl. lra.
  - replace (λ _ : ℝ, if Nat.eq_dec n k then INR (fact k) else 0) with (λ _ : ℝ, 0).
    2 : { extensionality x. simpl. destruct (Nat.eq_dec n k); try lia; lra. }
    pose proof (nth_derivative_at_pow_gt k n 0 ltac:(lia)) as H2; auto.
  - replace (λ _ : ℝ, if Nat.eq_dec n k then INR (fact k) else 0) with (λ _ : ℝ, 0).
    2 : { extensionality x. destruct (Nat.eq_dec n k); try lia; reflexivity. }
    pose proof nth_derivative_at_pow n k 0 ltac:(lia) as H2. replace (λ x : ℝ, n! / (n - k)! * 0 ^ (n - k)) with (λ x : ℝ, 0) in H2; auto.
    extensionality x. rewrite pow_i; try lia. lra.
Qed.

Lemma nth_derivative_at_sum : forall n m i (f : nat -> R -> R) a,
  (i <= m)%nat ->
  (forall k, (i <= k <= m)%nat -> nth_differentiable_at n (f k) a) ->
  ⟦ der ^ n a ⟧ (λ x, ∑ i m (λ k, f k x)) = (λ x, ∑ i m (λ k, (⟦ Der ^ n ⟧ (f k)) x)).
Proof.
  intros n m i f a H1 H2.
  induction m as [| k IH].
  - assert (i = 0)%nat by lia. subst.
    repeat rewrite sum_f_n_n. apply nth_derive_at_spec. apply H2; lia.
  - destruct (le_lt_dec i k) as [H3 | H3].
    + replace (λ x : ℝ, ∑ i (S k) (λ k0 : ℕ, f k0 x))
      with (λ x : ℝ, (∑ i k (λ k0 : ℕ, f k0 x)) + f (S k) x).
      2 : { extensionality x. rewrite sum_f_i_Sn_f; auto. }
      replace (λ x : ℝ, ∑ i (S k) (λ k0 : ℕ, (⟦ Der ^ n ⟧ (f k0)) x))
      with (λ x : ℝ, (∑ i k (λ k0 : ℕ, (⟦ Der ^ n ⟧ (f k0)) x)) + (⟦ Der ^ n ⟧ (f (S k))) x).
      2 : { extensionality x. rewrite sum_f_i_Sn_f; auto. }
      apply nth_derivative_at_plus.
      * apply IH; auto. intros j H4. apply H2. lia.
      * apply nth_derive_at_spec. apply H2. lia.
    + assert (i = S k)%nat by lia. subst.
      replace (λ x : ℝ, ∑ (S k) (S k) (λ k0 : ℕ, f k0 x)) with (f (S k)).
      2 : { extensionality x. rewrite sum_f_n_n. reflexivity. }
      replace (λ x : ℝ, ∑ (S k) (S k) (λ k0 : ℕ, (⟦ Der ^ n ⟧ (f k0)) x)) with (⟦ Der ^ n ⟧ (f (S k))).
      2 : { extensionality x. rewrite sum_f_n_n. reflexivity. } 
      apply nth_derive_at_spec. apply H2; lia.
Qed.

Lemma nth_derivative_sum : forall n m i (f : nat -> R -> R) (fn : nat -> R -> R),
  (i <= m)%nat ->
  (forall k, (i <= k <= m)%nat -> ⟦ der ^ n ⟧ (f k) = fn k) ->
  ⟦ der ^ n ⟧ (λ x, ∑ i m (λ k, f k x)) = (λ x, ∑ i m (λ k, fn k x)).
Proof.
  intros n m i f fn H1 H2.
  induction m as [| k IH].
  - assert (i = 0)%nat by lia. subst. 
    replace (λ x : ℝ, ∑ 0 0 (λ k : ℕ, f k x)) with (λ x : ℝ, f 0%nat x).
    2 : { extensionality x. rewrite sum_f_n_n. reflexivity. }
    replace (λ x : ℝ, ∑ 0 0 (λ k : ℕ, fn k x)) with (λ x : ℝ, fn 0%nat x).
    2 : { extensionality x. rewrite sum_f_n_n. reflexivity. }
    apply H2; lia.
  - destruct (le_lt_dec i k) as [H3 | H3].
    + replace (λ x : ℝ, ∑ i (S k) (λ k0 : ℕ, f k0 x))
      with (λ x : ℝ, (∑ i k (λ k0 : ℕ, f k0 x)) + f (S k) x).
      2 : { extensionality x. rewrite sum_f_i_Sn_f; auto. }
      replace (λ x : ℝ, ∑ i (S k) (λ k0 : ℕ, fn k0 x))
      with (λ x : ℝ, (∑ i k (λ k0 : ℕ, fn k0 x)) + fn (S k) x).
      2 : { extensionality x. rewrite sum_f_i_Sn_f; auto. }
      apply nth_derivative_plus.
      * apply IH; auto. intros j H4. apply H2. lia.
      * apply H2. lia.
    + assert (i = S k)%nat by lia. subst.
      replace (λ x : ℝ, ∑ (S k) (S k) (λ k0 : ℕ, f k0 x)) with (f (S k)).
      2 : { extensionality x. rewrite sum_f_n_n. reflexivity. }
      replace (λ x : ℝ, ∑ (S k) (S k) (λ k0 : ℕ, fn k0 x)) with (fn (S k)).
      2 : { extensionality x. rewrite sum_f_n_n. reflexivity. }
      apply H2; lia.
Qed.

Lemma nth_derivative_on_sum : forall n m i (f : nat -> R -> R) (fn : nat -> R -> R) D,
  differentiable_domain D ->
  (i <= m)%nat ->
  (forall k, (i <= k <= m)%nat -> ⟦ der ^ n ⟧ (f k) D = fn k) ->
  ⟦ der ^ n ⟧ (λ x, ∑ i m (λ k, f k x)) D = (λ x, ∑ i m (λ k, fn k x)).
Proof.
  intros n m i f fn D H1 H2 H3.
  induction m as [| k IH].
  - assert (i = 0)%nat by lia. subst.
    replace (λ x : ℝ, ∑ 0 0 (λ k : ℕ, f k x)) with (λ x : ℝ, f 0%nat x).
    2 : { extensionality x. rewrite sum_f_n_n. reflexivity. }
    replace (λ x : ℝ, ∑ 0 0 (λ k : ℕ, fn k x)) with (λ x : ℝ, fn 0%nat x).
    2 : { extensionality x. rewrite sum_f_n_n. reflexivity. }
    apply H3; lia.
  - destruct (le_lt_dec i k) as [H4 | H4].
    + replace (λ x : ℝ, ∑ i (S k) (λ k0 : ℕ, f k0 x))
      with (λ x : ℝ, (∑ i k (λ k0 : ℕ, f k0 x)) + f (S k) x).
      2 : { extensionality x. rewrite sum_f_i_Sn_f; auto. }
      replace (λ x : ℝ, ∑ i (S k) (λ k0 : ℕ, fn k0 x))
      with (λ x : ℝ, (∑ i k (λ k0 : ℕ, fn k0 x)) + fn (S k) x).
      2 : { extensionality x. rewrite sum_f_i_Sn_f; auto. }
      apply nth_derivative_on_plus; auto.
      * apply IH; auto. intros j H5. apply H3. lia.
    + assert (i = S k)%nat by lia. subst.
      replace (λ x : ℝ, ∑ (S k) (S k) (λ k0 : ℕ, f k0 x)) with (f (S k)).
      2 : { extensionality x. rewrite sum_f_n_n. reflexivity. }
      replace (λ x : ℝ, ∑ (S k) (S k) (λ k0 : ℕ, fn k0 x)) with (fn (S k)).
      2 : { extensionality x. rewrite sum_f_n_n. reflexivity. }
      apply H3; lia.
Qed.

Lemma nth_differentiable_derive : forall n f,
  nth_differentiable (S n) f -> nth_differentiable n (⟦ Der ⟧ f).
Proof.
  intros n f [fn' H1].
  apply nth_derivative_succ_iff in H1 as [f' [H2 H3]].
  exists fn'.
  assert (H4 : differentiable f).
  { eapply derivative_imp_differentiable; eauto. }
  apply derive_spec in H2; auto.
  rewrite H2. auto.
Qed.

Lemma nth_differentiable_on_derive : forall n f D,
  differentiable_domain D ->
  nth_differentiable_on (S n) f D -> 
  nth_differentiable_on n (⟦ Der ⟧ f D) D.
Proof.
  intros n f D H1 [fn' H2].
  apply nth_derivative_on_succ_iff in H2 as [f' [H2 H3]].
  exists fn'.
  apply nth_derivative_on_eq with (f1 := f'); auto.
  intros x H4. symmetry. apply derivative_on_imp_derive_on; auto.
Qed.

Lemma nth_derive_nth_differentiable : forall n m f,
  nth_differentiable (n + m) f -> nth_differentiable m (⟦ Der ^ n ⟧ f).
Proof.
  intros n. induction n as [| k IH].
  - intros m f H1. simpl. auto.
  - intros m f H1.
    rewrite nth_derive_succ.
    apply IH.
    apply nth_differentiable_derive; auto.
Qed.

Lemma nth_derive_on_nth_differentiable_on : forall n m f D,
  differentiable_domain D ->
  nth_differentiable_on (n + m) f D -> nth_differentiable_on m (⟦ Der ^ n ⟧ f D) D.
Proof.
  induction n as [| k IH]; intros m f D H1 H2.
  - simpl. auto.
  - rewrite nth_derive_on_succ. apply IH; auto.
    apply nth_differentiable_on_derive; auto.
Qed.

Lemma nth_differentiable_le : forall n m f,
  (n <= m)%nat -> nth_differentiable m f -> nth_differentiable n f.
Proof.
  intros n m f H1 [fn H2].
  eapply nth_derivative_le_differentiable; eauto.
Qed.

Lemma nth_differentiable_on_le : forall n m f D,
  (n <= m)%nat -> nth_differentiable_on m f D -> nth_differentiable_on n f D.
Proof.
  intros n m f D H1 [fn H2].
  eapply nth_derivative_on_le_differentiable; eauto.
Qed.

Lemma nth_derive_minus : forall n f g,
  nth_differentiable n f ->
  nth_differentiable n g ->
  ⟦ Der ^ n ⟧ (f - g) = (⟦ Der ^ n ⟧ f - ⟦ Der ^ n ⟧ g)%f.
Proof.
  intros n f g H1 H2.
  apply nth_derivative_imp_nth_derive.
  apply nth_derivative_minus; auto; apply nth_derive_spec; auto.
Qed.

Lemma nth_derive_at_mult_const_l : forall n c f,
  nth_differentiable n f ->
  ⟦ Der ^ n ⟧ (λ x, c * f x) = (λ x, c * (⟦ Der ^ n ⟧ f) x).
Proof.
  intros n c f H1.
  apply nth_derivative_imp_nth_derive.
  apply nth_derivative_mult_const_l; auto; apply nth_derive_spec; auto.
Qed.

Lemma nth_derive_sum : forall (i n m : nat) (f : nat -> R -> R),
  (i <= m)%nat -> (forall k, nth_differentiable n (f k)) ->
  ⟦ Der ^ n ⟧ (λ x, ∑ i m (λ k, f k x)) = (λ x, ∑ i m (λ k, (⟦ Der ^ n ⟧ (f k)) x)).
Proof.
  intros i n m f H1 H2. apply nth_derivative_imp_nth_derive. apply nth_derivative_sum; auto.
  intros k H3. apply nth_derive_spec. apply H2.
Qed.

Lemma nth_derive_at_sum : forall (i n m : nat) (a : R) (f : nat -> R -> R),
  (i <= m)%nat -> (forall k, nth_differentiable n (f k)) ->
  ⟦ Der ^ n a ⟧ (λ x, ∑ i m (λ k, f k x)) = (∑ i m (λ k, ⟦ Der ^ n a ⟧ (f k))).
Proof.
  intros i n m a f H1 H2.
  unfold nth_derive_at.
  rewrite nth_derive_sum; auto.
Qed.

Lemma nth_derive_on_sum : forall (i n m : nat) (f : nat -> R -> R) D x,
  differentiable_domain D ->
  (i <= m)%nat ->
  x ∈ D ->
  (forall k, (i <= k <= m)%nat -> nth_differentiable_on n (f k) D) ->
  ⟦ Der ^ n ⟧ (λ x, ∑ i m (λ k, f k x)) D x = ∑ i m (λ k, ⟦ Der ^ n ⟧ (f k) D x).
Proof.
  intros i n m f D x H1 H2 H3 H4.
  apply nth_derivative_on_imp_nth_derive_on with (f' := λ y, ∑ i m (λ k, ⟦ Der ^ n ⟧ (f k) D y)); auto.
  apply nth_derivative_on_sum; auto.
  intros k H5. specialize (H4 k H5) as [fk H4].
  apply nth_derivative_on_ext with (f1' := fk); auto.
  intros y H6. symmetry. apply nth_derivative_on_imp_nth_derive_on; auto.
Qed.

Lemma derivative_shift : forall f f' c,
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ (λ x, f (x - c)) = (λ x, f' (x - c)).
Proof.
  intros f f' c H1 x.
  unfold derivative_at.
  replace (λ h, (f (x + h - c) - f (x - c)) / h) with (λ h, (f (x - c + h) - f (x - c)) / h).
  2 : { extensionality h. replace (x + h - c) with (x - c + h) by lra. reflexivity. }
  apply H1.
Qed.

Lemma nth_derivative_shift : forall n f fn' c,
  ⟦ der^n ⟧ f = fn' -> ⟦ der^n ⟧ (λ x, f (x - c)) = (λ x, fn' (x - c)).
Proof.
  induction n as [| k IH]; intros f fn' c H1.
  - simpl in *. subst. reflexivity.
  - simpl in *. destruct H1 as [f' [H2 H3]].
    exists (λ x, f' (x - c)). split.
    + apply IH; auto.
    + intros x. unfold derivative_at.
      replace (λ h, (f' (x + h - c) - f' (x - c)) / h) with (λ h, (f' (x - c + h) - f' (x - c)) / h).
      2 : { extensionality h. replace (x + h - c) with (x - c + h) by lra. reflexivity. }
      apply H3.
Qed.

Lemma derivative_pow_shift : forall n c,
  ⟦ der ⟧ (λ x, (x - c) ^ n) = (λ x, INR n * (x - c) ^ (n - 1)).
Proof.
  intros n c. pose proof derivative_shift (λ x, x ^ n) (λ x, n * x ^ (n - 1)) c as H1.
  apply H1. apply derivative_pow.
Qed.

Lemma nth_derivative_pow_shift_gt : forall k i a,
  (k > i)%nat -> ⟦ der^k ⟧ (λ x, (x - a) ^ i) = (λ _, 0).
Proof.
  intros k i a H1.
  pose proof nth_derivative_shift k (λ x, x ^ i) (λ x, 0) a as H2.
  apply H2. apply nth_derivative_pow_gt; auto.
Qed.

Lemma nth_derivative_pow_shift : forall n k c,
  (k <= n)%nat ->
  ⟦ der^k ⟧ (λ x, (x - c) ^ n) = (λ x, (n! / (n - k)!) * (x - c) ^ (n - k)).
Proof.
  intros n k c H1.
  pose proof nth_derivative_shift k (λ x, x ^ n) (λ x, (n! / (n - k)!) * x ^ (n - k)) c as H2.
  apply H2. apply nth_derivative_pow; auto.
Qed.

Lemma nth_derivative_at_pow_shift_zero : forall n k a,
  (k < n)%nat ->
  ⟦ der^k a ⟧ (λ x, (x - a) ^ n) = (λ x, 0).
Proof.
  intros n k a H1.
  pose proof nth_derivative_pow_shift n k a (ltac:(lia)) as H2.
  apply nth_derivative_imp_at with (a := a) in H2.
  apply nth_derivative_at_ext_val with (f' := λ x : ℝ, n! / (n - k)! * (x - a) ^ (n - k)); auto.
  rewrite Rminus_diag, pow_i; try lia; try lra.
Qed.

Lemma nth_derive_shift : forall n f c,
  nth_differentiable n f ->
  ⟦ Der ^ n ⟧ (λ x, f (x - c)) = (λ x, (⟦ Der ^ n ⟧ f) (x - c)).
Proof.
  intros n f c H1.
  apply nth_derivative_imp_nth_derive.
  apply nth_derivative_shift.
  apply nth_derive_spec.
  apply H1.
Qed.

Lemma nth_derive_at_shift : forall n f c a,
  nth_differentiable n f ->
  ⟦ Der ^ n a ⟧ (λ x, f (x - c)) = ⟦ Der ^ n (a - c) ⟧ f.
Proof.
  intros n f c a H1.
  unfold nth_derive_at.
  rewrite nth_derive_shift; auto.
Qed.

Lemma nth_derive_pow_shift : forall n c,
  ⟦ Der ^ n ⟧ (λ x, (x - c) ^ n) = (λ _, n!).
Proof.
  intros n c.
  apply nth_derivative_imp_nth_derive.
  pose proof nth_derivative_shift n (λ x, x ^ n) (λ _, INR (fact n)) c as H1.
  apply H1.  
  replace (λ _ : ℝ, INR (fact n)) with (λ x : ℝ, INR (fact n) / INR (fact (n - n)) * x ^ (n - n)).
  2 : {   extensionality x. rewrite Nat.sub_diag. simpl. lra. }
  apply nth_derivative_pow; lia.
Qed.

Lemma nth_derivative_derive : forall n f,
  nth_differentiable (S n) f ->
  ⟦ der ^ n ⟧ (⟦ Der ⟧ f) = ⟦ Der ^ (S n) ⟧ f.
Proof.
  intros n f H1.
  rewrite nth_derive_succ.
  apply nth_derive_spec.
  apply nth_differentiable_derive; auto.
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
  - subst k. apply lhopital_0_0_strong with (f' := ⟦ Der ⟧ f) (g' := ⟦ Der ⟧ g); auto.
    -- specialize (H4 0%nat ltac:(lia)); auto.
    -- specialize (H5 0%nat ltac:(lia)); auto. 
    -- apply derive_spec; try reflexivity. specialize (H2 1%nat ltac:(lia)) as H8. apply nth_differentiable_imp_differentiable with (n := 1%nat) in H2; auto.
    -- apply derive_spec; try reflexivity. specialize (H3 1%nat ltac:(lia)) as H8. apply nth_differentiable_imp_differentiable with (n := 1%nat) in H3; auto.
    -- exists 1. split; try lra. intros x H7 _. apply derive_spec; auto. apply nth_differentiable_imp_differentiable with (n := 1%nat); auto.
    -- exists 1. split; try lra. intros x H7 _. apply derive_spec; auto. apply nth_differentiable_imp_differentiable with (n := 1%nat); auto.
    -- apply (H1 0%nat); lia.
  - apply lhopital_0_0_strong with (f' := ⟦ Der ⟧ f) (g' := ⟦ Der ⟧ g); auto.
    -- specialize (H4 0%nat ltac:(lia)); auto.
    -- specialize (H5 0%nat ltac:(lia)); auto.
    -- apply derive_spec; try reflexivity. specialize (H2 1%nat ltac:(lia)) as H8. apply nth_differentiable_imp_differentiable with (n := 1%nat); auto.
    -- apply derive_spec; try reflexivity. specialize (H3 1%nat ltac:(lia)) as H8. apply nth_differentiable_imp_differentiable with (n := 1%nat); auto.
    -- exists 1. split; try lra. intros x H8 _. apply derive_spec; auto. apply nth_differentiable_imp_differentiable with (n := 1%nat); auto.
    -- exists 1. split; try lra. intros x H8 _. apply derive_spec; auto. apply nth_differentiable_imp_differentiable with (n := 1%nat); auto.
    -- apply (H1 0%nat); lia.
    -- apply IH; auto.
       ++ intros i H8. specialize (H1 (S i) ltac:(lia)) as [δ [H9 H10]].
          exists δ. split; auto. intros x H11 H12. rewrite <- nth_derive_at_succ.
          apply H10; auto.
       ++ intros i H8. apply nth_differentiable_derive. apply H2; lia.
       ++ intros i H8. apply nth_differentiable_derive. apply H3; lia.
       ++ intros i H8. rewrite <- nth_derive_succ. apply H4; lia.
       ++ intros i H8. rewrite <- nth_derive_succ. apply H5; lia.
       ++ repeat rewrite <- nth_derive_succ. apply H6.
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
  apply lhopital_0_0_strong with (f' := ⟦ Der ⟧ f D) (g' := ⟦ Der ⟧ g D).
  - specialize (H4 0%nat ltac:(lia)). simpl in H4. rewrite <- H4.
    apply differentiable_at_imp_continuous_at.
    apply nth_differentiable_on_imp_differentiable_at with (n := 1%nat) (D := D); auto.
    destruct H1 as [δ [H9 H10]]. apply H10; solve_R. apply H7; lia.
  - specialize (H5 0%nat ltac:(lia)). simpl in H5. rewrite <- H5.
    apply differentiable_at_imp_continuous_at.
    apply nth_differentiable_on_imp_differentiable_at with (n := 1%nat) (D := D); auto.
    destruct H1 as [δ [H9 H10]]. apply H10; solve_R. apply H8; lia.
  - apply derive_on_spec_at; auto. apply nth_differentiable_on_imp_differentiable_on with (n := 1%nat); try lia.
    apply H7; lia.
  - apply derive_on_spec_at; auto. apply nth_differentiable_on_imp_differentiable_on with (n := 1%nat); try lia.
    apply H8; lia.
  - destruct H1 as [δ [H9 H10]]. exists δ. split; auto. intros x H11 H12.
    apply derivative_on_imp_derivative_at with (D := D).
    -- exists (Rmin (x - (a - δ)) (a + δ - x)). split; [solve_R |]. intros y H13. apply (H10 y ltac:(solve_R)).
    -- apply derive_on_imp_derivative_on; auto.
       apply nth_differentiable_on_imp_differentiable_on with (n := 1%nat); auto; try lia.
       apply H7. lia.
  - destruct H1 as [δ [H9 H10]]. exists δ. split; auto. intros x H11 H12.
    apply derivative_on_imp_derivative_at with (D := D).
    -- exists (Rmin (x - (a - δ)) (a + δ - x)). split; [solve_R |]. intros y H13. apply (H10 y ltac:(solve_R)).
    -- apply derive_on_imp_derivative_on; auto.
       apply nth_differentiable_on_imp_differentiable_on with (n := 1%nat); auto; try lia.
       apply H8. lia.
  - apply (H0 0%nat); lia.
  - assert (H9 : differentiable_domain D).
    { 
      intros x H9. pose proof (nth_differentiable_on_imp_differentiable_on (S k) f D ltac:(lia) H2) as H10.
      specialize (H10 x H9) as [[H11 H12] | [[H11 H12] | [H11 H12]]]; auto.
    }
   apply IH.
    + apply nth_differentiable_on_derive; auto.
    + intros i H10. rewrite <- nth_derive_on_succ. apply H4; lia.
    + intros i H10. apply nth_differentiable_on_derive; auto. apply H7; lia.
    + apply nth_differentiable_on_derive; auto.
    + intros i H10. rewrite <- nth_derive_on_succ. apply H5; lia.
    + repeat rewrite <- nth_derive_on_succ; auto.
    + intros i H10. rewrite <- nth_derive_on_succ; apply H0; lia.
    + intros i H10. apply nth_differentiable_on_le with (m := k); auto. apply nth_differentiable_on_derive; auto.
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
  auto_interval.
Qed.

Lemma derive_on_eq_derive_at_interior : forall f D x,
  interior_point D x ->
  (⟦ Der ⟧ f D) x = (⟦ Der ⟧ f) x.
Proof.
  intros f D x H1.
  unfold derive_on.
  assert (exists y, is_derive_on_limit_at_point f D x y) as H2.
  { exists (⟦ Der x ⟧ f). left. split; auto. }
  pose proof (epsilon_spec (inhabits 0) (is_derive_on_limit_at_point f D x) H2) as H3.
  destruct H3 as [[_ H3] | [[H3 _] | [[H3 _] | [H3 _]]]]; auto_interval.
Qed.

Lemma nth_derive_on_eq_nth_derive_at_interior : forall n f D a,
  interior_point D a ->
  nth_differentiable_on n f D ->
  (⟦ Der^n ⟧ f D) a = ⟦ Der^n a ⟧ f.
Proof.
  intros n f D a H1 H2.
  destruct H1 as [δ [H1 H3]].
  assert (H4: forall x, |x - a| < δ -> ⟦ Der^n ⟧ f D x = (⟦ Der^n ⟧ f) x).
  {
    induction n as [|k IH]; intros x H4; auto.
    simpl. rewrite derive_on_eq_derive_at_interior.
    - apply derive_at_eq. exists (δ - |x - a|). split; [ solve_R | ].
      intros y Hy. apply IH; [ | solve_R ].
      apply nth_differentiable_on_le with (m := S k); solve_R.
    - exists (δ - |x - a|). split; [ solve_R | ].
      intros y Hy. apply H3. solve_R.
  }
  specialize (H4 a ltac:(solve_R)). auto.
Qed.

Lemma derive_on_open_eq_derive : forall f D x,
  (forall y, y ∈ D -> interior_point D y) ->
  x ∈ D ->
  ⟦ Der ⟧ f D x = (⟦ Der ⟧ f) x.
Proof.
  intros f D x H1 H2.
  unfold derive_on.
  assert (H3 : is_derive_on_limit_at_point f D x = (fun y => y = ⟦ Der x ⟧ f)).
  {
    extensionality y.
    unfold is_derive_on_limit_at_point.
    apply propositional_extensionality.
    split.
    - intros [H3 | [H3 | [H3 | H3]]].
      + destruct H3; auto.
      + destruct H3 as [H3 _]. specialize (H1 x H2). auto_interval.
      + destruct H3 as [H3 _]. specialize (H1 x H2). auto_interval.
      + destruct H3 as [H3 _]. specialize (H1 x H2). contradiction.
    - intros H3. left. split; auto.
  }
  rewrite H3. apply epsilon_spec.
  exists (⟦ Der x ⟧ f). reflexivity.
Qed.

Lemma nth_derive_on_open_eq_nth_derive : forall n f D,
  (forall y, y ∈ D -> interior_point D y) ->
  nth_differentiable_on n f D ->
  forall x, x ∈ D -> (⟦ Der^n ⟧ f D) x = (⟦ Der^n ⟧ f) x.
Proof.
  induction n as [| k IH].
  - simpl. auto.
  - intros f D H1 H2 x H3.
    simpl.
    rewrite derive_on_open_eq_derive; auto.
    apply derive_at_eq.
    destruct (H1 x H3) as [δ [H4 H5]].
    exists δ. split; auto.
    intros y H6.
    apply IH; auto.
    apply nth_differentiable_on_le with (m := S k); try lia; auto.
    apply H5. solve_R.
Qed.

Lemma lhopital_nth_neighborhood : forall (n : nat) f g a L,
  (exists δ, δ > 0 /\ nth_differentiable_on n f (a - δ, a + δ)) ->
  (exists δ, δ > 0 /\ nth_differentiable_on n g (a - δ, a + δ)) ->
  (forall k, (k < n)%nat -> (⟦ Der^k a ⟧ f) = 0) ->
  (forall k, (k < n)%nat -> (⟦ Der^k a ⟧ g) = 0) ->
  (forall k, (k < n)%nat -> exists δ, δ > 0 /\ forall x, x ∈ (a - δ, a + δ) -> x <> a -> (⟦ Der^(S k) ⟧ g) x <> 0) ->
  ⟦ lim a ⟧ ( (⟦ Der^n ⟧ f) / (⟦ Der^n ⟧ g) ) = L ->
  ⟦ lim a ⟧ ( f / g ) = L.
Proof.
  intros n f g a L [δ1 [H1 H2]] [δ2 [H3 H4]] H5 H6 H7 H8.
  set (δ := Rmin δ1 δ2).
  assert (H9 : nth_differentiable_on n f (a - δ, a + δ)).
  { unfold δ in *. apply nth_differentiable_on_subset with (D1 := (a - δ1, a + δ1)); auto. apply differentiable_domain_open; solve_R. intros x H9. solve_R. }
  assert (H10 : nth_differentiable_on n g (a - δ, a + δ)).
  { unfold δ in *. apply nth_differentiable_on_subset with (D1 := (a - δ2, a + δ2)); auto. apply differentiable_domain_open; solve_R. intros x H10. solve_R. }
  apply lhopital_nth_open with (n := n) (a := a - δ) (b := a + δ) (c := a); auto.
  - unfold δ; solve_R.
  - intros k H11. unfold δ in *. rewrite nth_derive_on_eq_nth_derive_at_interior; auto. auto_interval.
    apply nth_differentiable_on_le with (m := n); try lia; auto.
  - intros k Hk. unfold δ in *. rewrite nth_derive_on_eq_nth_derive_at_interior; auto. auto_interval.
    apply nth_differentiable_on_le with (m := n); try lia; auto.
  - intros k H11. specialize (H7 k H11) as [δ3 [H12 H13]].
    exists (Rmin δ δ3). split; [solve_R |].
    intros x H14 H15.
    rewrite nth_derive_on_open_eq_nth_derive with (D := (a - δ, a + δ)); auto.
    + apply H13; try solve_R.
    + intros y H16. auto_interval.
    + apply nth_differentiable_on_le with (m := n); try lia; auto.
    + solve_R.
  - apply limit_eq with (f1 := (⟦ Der^n ⟧ f / ⟦ Der^n ⟧ g)%f); auto.
    exists δ. split; [unfold δ; solve_R |].
    intros x H11.
    assert (H12 : x ∈ (a - δ, a + δ)) by solve_R.
    rewrite nth_derive_on_open_eq_nth_derive with (D := (a - δ, a + δ)); auto.
    2 : { intros y H13. auto_interval. }
    rewrite nth_derive_on_open_eq_nth_derive with (f := g) (D := (a - δ, a + δ)); auto; try (intros y Hy; apply is_interior_point_open; solve_R).
    intros y H13. auto_interval.
Qed.