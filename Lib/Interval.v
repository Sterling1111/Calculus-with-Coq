From Lib Require Import Imports Sets Notations Reals_util.
Import SetNotations.

Declare Scope interval_scope.
Delimit Scope interval_scope with interval.

Module IntervalNotations.
  Notation "[ a , b ]" := (fun x => a <= x <= b) : interval_scope.
  Notation "[ a , b )" := (fun x => a <= x < b) : interval_scope.
  Notation "( a , b ]" := (fun x => a < x <= b)  : interval_scope.
  Notation "( a , b )" := (fun x => a < x < b) : interval_scope.

  Notation "(-∞ , b )" := (fun x => x < b) : interval_scope.
  Notation "( -∞ , b ]" := (fun x => x <= b) : interval_scope.
  Notation "( a , ∞)" := (fun x => a < x) : interval_scope.
  Notation "[ a , ∞)" := (fun x => a <= x) : interval_scope.

  Notation "(-∞ , +∞)" := (Full_set _) : interval_scope.
End IntervalNotations.

Import IntervalNotations.
Open Scope interval_scope.

Definition left_endpoint (A : Ensemble R) (a : R) :=
  exists δ, δ > 0 /\ forall x, (x ∈ [a-δ, a) -> x ∉ A) /\ (x ∈ [a, a+δ) -> x ∈ A).

Definition right_endpoint (A : Ensemble R) (a : R) :=
  exists δ, δ > 0 /\ forall x, (x ∈ (a, a+δ] -> x ∉ A) /\ (x ∈ (a-δ, a] -> x ∈ A).

Definition interior_point (A : Ensemble R) (a : R) :=
  exists δ, δ > 0 /\ forall x, x ∈ (a-δ, a+δ) -> x ∈ A.

Definition isolated_point (A : Ensemble R) (a : R) :=
  a ∈ A /\ (exists δ, δ > 0 /\ forall x, x ∈ (a-δ, a) ⋃ (a, a+δ) -> x ∉ A).

Lemma full_interior : forall a,
  interior_point (Full_set R) a.
Proof.
  intros a. exists 1. split; solve_R. apply Full_intro.
Qed.

Lemma full_not_left_pt : forall a,
  ~ left_endpoint (Full_set R) a.
Proof.
  intros a [δ [H1 H2]].
  specialize (H2 (a - δ)) as [H2 _]. apply H2.
  - solve_R.
  - apply Full_intro.
Qed.

Lemma full_not_right_pt : forall a,
  ~ right_endpoint (Full_set R) a.
Proof.
  intros a. intros [δ [H1 H2]].
  specialize (H2 (a + δ)) as [H2 _]. apply H2.
  - solve_R.
  - apply Full_intro.
Qed.

Lemma open_interior_iff : forall a b x,
  a < b -> (x ∈ (a, b) <-> interior_point (a, b) x).
Proof.
  intros a b x H1. split.
  - intro H2. exists (Rmin (x - a) (b - x)). split; solve_R.
  - intros [δ [H2 H3]].
    specialize (H3 x ltac:(solve_R)). auto.
Qed.

Lemma open_not_left_pt : forall a b x,
  a < b -> ~left_endpoint (a, b) x.
Proof.
  intros a b x H1 [δ [H2 H3]].
  assert (H4 : a < x < b).
  { specialize (H3 x). solve_R. }
  set (ε := Rmin (x - a) δ).
  specialize (H3 (x - ε/2)) as [H5 H6].
  apply H5; unfold ε in *; solve_R.
Qed.

Lemma open_not_right_pt : forall a b x,
  a < b -> ~right_endpoint (a, b) x.
Proof.
  intros a b x H1 [δ [H2 H3]].
  assert (H4 : a < x < b).
  { specialize (H3 x). solve_R. }
  set (ε := Rmin (b - x) δ).
  specialize (H3 (x + ε/2)) as [H5 H6].
  apply H5; unfold ε in *; solve_R.
Qed.

Lemma closed_interior_iff : forall a b x,
  a < b -> (x ∈ (a, b) <-> interior_point [a, b] x).
Proof.
  intros a b x H1. split.
  - intros H2.
    exists (Rmin (x - a) (b - x)). split; solve_R.
  - intros [δ [H2 H3]].
    assert (x = a \/ x <> a) as [H4 | H4] by lra.
    -- specialize (H3 (a - δ/2) ltac:(solve_R)). solve_R.
    -- assert (x = b \/ x <> b) as [H5 | H5] by lra.
       * specialize (H3 (b + δ/2) ltac:(solve_R)). solve_R.
       * specialize (H3 x ltac:(solve_R)). solve_R.
Qed.

Lemma closed_not_interior_a : forall a b,
  a < b -> ~interior_point [a, b] a.
Proof.
  intros a b H1 [δ [H2 H3]].
  specialize (H3 (a - δ / 2) ltac:(solve_R)).
  solve_R.
Qed.

Lemma closed_not_interior_b : forall a b,
  a < b -> ~interior_point [a, b] b.
Proof.
  intros a b H1 [δ [H2 H3]].
  specialize (H3 (b + δ / 2) ltac:(solve_R)). solve_R.
Qed.

Lemma closed_left_pt_val : forall a b,
  a < b -> left_endpoint [a, b] a.
Proof.
  intros a b H1.
  exists (b - a). split; try lra.
  intros x. split; solve_R.
Qed.

Lemma closed_left_pt_iff : forall a b x,
  a < b -> (left_endpoint [a, b] x <-> x = a).
Proof.
  intros a b x H1. split.
  - intros [δ [H2 H3]]. pose proof Rtotal_order x a as [H4 | [H4 | H4]]; auto.
    -- specialize (H3 x) as [_ H3]. specialize (H3 ltac:(solve_R)). solve_R.
    -- assert (x > b \/ x <= b) as [H5 | H5] by lra.
       * specialize (H3 x) as [_ H3]. specialize (H3 ltac:(solve_R)). solve_R.
       * destruct H5 as [H5 | H5].
         2 : { specialize (H3 (x - Rmin (b - a) δ)) as [H3 _]. specialize (H3 ltac:(solve_R)). solve_R. }
        assert (H6 : a < x < b) by lra.
        clear H1 H4 H5. rename H6 into H1.
        specialize (H3 (Rmax a (x - δ))) as [H3 _].
        specialize (H3 ltac:(solve_R)). solve_R.
  - intros H2. subst. exists (b - a). split; solve_R.
Qed.

Lemma closed_not_left_pt_b : forall a b,
  a < b -> ~left_endpoint [a, b] b.
Proof.
  intros a b H1 [δ [H2 H3]].
  specialize (H3 (b + δ / 2)) as [H3 H4]. solve_R.
Qed.

Lemma closed_not_left_pt_interior : forall a b x,
  a < b -> x ∈ (a, b) -> ~left_endpoint [a, b] x.
Proof.
  intros a b x H1 H2 [δ [H3 H4]].
  assert (H5 : a < x <= b). { solve_R. }
  set (ε := Rmin (x - a) δ). specialize (H4 (x - ε/2)) as [H6 H7].
  apply H6; unfold ε in *; solve_R.
Qed.

Lemma closed_right_pt_val : forall a b,
  a < b -> right_endpoint [a, b] b.
Proof.
  intros a b H1.
  exists (b - a). split; try lra.
  intros x. solve_R.
Qed.

Lemma closed_right_pt_iff : forall a b x,
  a < b -> (right_endpoint [a, b] x <-> x = b).
Proof.
  intros a b x H1. split.
  - intros [δ [H2 H3]].
    pose proof Rtotal_order x b as [H4 | [H4 | H4]]; auto.
    + assert (x < a \/ x >= a) as [H5 | H5] by lra.
      * specialize (H3 x) as [_ H3]. specialize (H3 ltac:(solve_R)). solve_R.
      * specialize (H3 (Rmin b (x + δ))) as [H3 _]. specialize (H3 ltac:(solve_R)). solve_R.
    + specialize (H3 x) as [_ H3]. specialize (H3 ltac:(solve_R)). solve_R.
  - intros H2. subst. exists (b - a). split; solve_R.
Qed.

Lemma closed_not_right_pt_a : forall a b,
  a < b -> ~right_endpoint [a, b] a.
Proof.
  intros a b H1 [δ [H2 H3]].
  specialize (H3 (a - δ / 2)) as [H3 H4]; solve_R.
Qed.

Lemma closed_not_right_pt_interior : forall a b x,
  a < b -> x ∈ (a, b) -> ~right_endpoint [a, b] x.
Proof.
  intros a b x H1 H2 [δ [H3 H4]].
  assert (H5 : a <= x < b). { solve_R. }
  set (ε := Rmin (b - x) δ). specialize (H4 (x + ε/2)) as [H6 H7].
  apply H6; unfold ε in *; solve_R.
Qed.

Lemma lopen_interior_iff : forall a b x,
  a < b -> (x ∈ (a, b) <-> interior_point (a, b] x).
Proof.
  intros a b x H1. split.
  - intros H2.
    exists (Rmin (x - a) (b - x)). split; solve_R.
  - intros [δ [H2 H3]].
    assert (H4 : x ∈ (x - δ, x + δ)) by solve_R.
    specialize (H3 x H4) as H5.
    assert (x = b \/ x < b) as [H6 | H6] by solve_R.
    -- subst x. specialize (H3 (b + δ/2)). solve_R. 
    -- split; solve_R.
Qed.

Lemma lopen_not_interior_b : forall a b,
  a < b -> ~interior_point (a, b] b.
Proof.
  intros a b H1 [δ [H2 H3]].
  specialize (H3 (b + δ / 2)). solve_R.
Qed.

Lemma lopen_not_left_pt : forall a b x,
  a < b -> ~left_endpoint (a, b] x.
Proof.
  intros a b x H1 [δ [H2 H3]].
  assert (H4 : a < x <= b). { specialize (H3 x). solve_R. }
  set (ε := Rmin (x - a) δ).
  specialize (H3 (x - ε/2)) as [H5 H6].
  apply H5; unfold ε in *; solve_R.
Qed.

Lemma lopen_right_pt_val : forall a b,
  a < b -> right_endpoint (a, b] b.
Proof.
  intros a b H1.
  exists (b - a). split; try lra.
  intros x. split; solve_R.
Qed.

Lemma lopen_right_pt_iff : forall a b x,
  a < b -> (right_endpoint (a, b] x <-> x = b).
Proof.
  intros a b x H1. split.
  - intros [δ [H2 H3]].
    pose proof Rtotal_order x b as [H4 | [H4 | H4]]; auto.
    + assert (x <= a \/ x > a) as [H5 | H5] by lra.
      * specialize (H3 x) as [_ H3]. solve_R.
      * specialize (H3 (Rmin b (x + δ))) as [H3 _]. solve_R.
    + specialize (H3 x) as [_ H3]. solve_R.
  - intros H2. subst. exists (b - a). split; solve_R.
Qed.

Lemma lopen_not_right_pt_interior : forall a b x,
  a < b -> x ∈ (a, b) -> ~right_endpoint (a, b] x.
Proof.
  intros a b x H1 H2 [δ [H3 H4]].
  assert (H5 : a < x < b). { solve_R. }
  set (ε := Rmin (b - x) δ).
  specialize (H4 (x + ε/2)) as [H6 H7].
  apply H6; unfold ε in *; solve_R.
Qed.

Lemma ropen_interior_iff : forall a b x,
  a < b -> (x ∈ (a, b) <-> interior_point [a, b) x).
Proof.
  intros a b x H1. split.
  - intros H2. exists (Rmin (x - a) (b - x)).
    split; try solve_R.
  - intros [δ [H2 H3]].
    assert (H4 : x ∈ (x - δ, x + δ)) by solve_R.
    specialize (H3 x H4) as H5.
    assert (x = a \/ x > a) as [H6 | H6] by solve_R.
    + subst x. specialize (H3 (a - δ/2)). solve_R.
    + split; solve_R.
Qed.

Lemma ropen_not_interior_a : forall a b,
  a < b -> ~interior_point [a, b) a.
Proof.
  intros a b H1 [δ [H2 H3]]. 
  specialize (H3 (a - δ / 2)). solve_R.
Qed.

Lemma ropen_left_pt_val : forall a b,
  a < b -> left_endpoint [a, b) a.
Proof.
  intros a b H1.
  exists (b - a). split; try lra.
  intros x. split; solve_R.
Qed.

Lemma ropen_left_pt_iff : forall a b x,
  a < b -> (left_endpoint [a, b) x <-> x = a).
Proof.
  intros a b x H1. split.
  - intros [δ [H2 H3]].
    assert (H4 : x ∈ [a, b)).
    { specialize (H3 x). solve_R. }
    assert (x = a \/ x < a \/ x > a) as [H5 | [H5 | H5]] by solve_R; auto.
    + specialize (H3 x). solve_R.
    + assert (x >= b \/ a < x < b) as [H6 | H6] by solve_R.
      * specialize (H3 x). solve_R.
      * specialize (H3 (x - Rmin (x - a) (δ/2))) as [H7 _]. 
        solve_R.
  - intros H2. subst. apply ropen_left_pt_val; auto.
Qed.

Lemma ropen_not_left_pt_interior : forall a b x,
  a < b -> x ∈ (a, b) -> ~left_endpoint [a, b) x.
Proof.
  intros a b x H1 H2 [δ [H3 H4]].
  assert (H5 : a < x < b). { solve_R. }
  set (ε := Rmin (x - a) δ).
  specialize (H4 (x - ε/2)) as [H6 H7].
  apply H6; unfold ε in *; solve_R.
Qed.

Lemma ropen_not_right_pt : forall a b x,
  a < b -> ~right_endpoint [a, b) x.
Proof.
  intros a b x H1 [δ [H2 H3]].
  assert (H4 : a <= x < b). { specialize (H3 x). solve_R. }
  set (ε := Rmin (b - x) δ).
  specialize (H3 (x + ε/2)) as [H5 H6].
  apply H5; unfold ε in *; solve_R.
Qed.

Lemma interior_not_endpoint : forall A a,
  interior_point A a -> ~ (left_endpoint A a \/ right_endpoint A a).
Proof.
  intros A a [δ [H1 H2]]. apply and_not_or. split; intros [δ' [H3 H4]].
  - set (x := a - Rmin (δ/2) (δ'/2)).
    destruct (H4 x) as [H5 H6].
    assert (H7 : x ∈ [a - δ', a)) by (unfold x; solve_R).
    assert (H8 : x ∈ A) by (apply H2; unfold x; solve_R).
    specialize (H5 H7).
    contradiction.
  - set (x := a + Rmin (δ/2) (δ'/2)).
    destruct (H4 x) as [H5 H6].
    assert (H7 : x ∈ (a, a + δ']) by (unfold x; solve_R).
    assert (H8 : x ∈ A) by (apply H2; unfold x; solve_R).
    specialize (H5 H7).
    contradiction.
Qed.

Lemma left_endpoint_not_interior : forall A a,
  left_endpoint A a -> ~ interior_point A a.
Proof.
  intros A a [d1 [H1 H2]] [d2 [H3 H4]].
  set (x := a - Rmin d1 d2 / 2).
  assert (H5 : x ∈ [a - d1, a)). { unfold x; solve_R. }
  assert (H6 : x ∈ (a - d2, a + d2)). { unfold x; solve_R. }
  specialize (H2 x) as [H2 _].
  specialize (H2 H5).
  apply H4 in H6.
  contradiction.
Qed.

Lemma right_endpoint_not_interior : forall A a,
  right_endpoint A a -> ~ interior_point A a.
Proof.
  intros A a [d1 [H1 H2]] [d2 [H3 H4]].
  set (x := a + Rmin d1 d2 / 2).
  assert (H5 : x ∈ (a, a + d1]). { unfold x; solve_R. }
  assert (H6 : x ∈ (a - d2, a + d2)). { unfold x; solve_R. }
  specialize (H2 x) as [H2 _].
  specialize (H2 H5).
  apply H4 in H6.
  contradiction.
Qed.

Lemma right_endpoint_not_left_endpoint : forall A a,
  right_endpoint A a -> ~ left_endpoint A a.
Proof.
  intros A a [d1 [H1 H2]] [d2 [H3 H4]].
  set (x := a - Rmin d1 d2 / 2).
  assert (H5 : x ∈ (a - d1, a]). { unfold x; solve_R. }
  assert (H6 : x ∈ [a - d2, a)). { unfold x; solve_R. }
  specialize (H2 x) as [_ H2].
  specialize (H4 x) as [H4 _].
  specialize (H2 H5).
  specialize (H4 H6).
  contradiction.
Qed.

Lemma left_endpoint_not_right_endpoint : forall A a,
  left_endpoint A a -> ~ right_endpoint A a.
Proof.
  intros A a [d1 [H1 H2]] [d2 [H3 H4]].
  set (x := a + Rmin d1 d2 / 2).
  assert (H5 : x ∈ [a, a + d1)). { unfold x; solve_R. }
  assert (H6 : x ∈ (a, a + d2]). { unfold x; solve_R. }
  specialize (H2 x) as [_ H2].
  specialize (H4 x) as [H4 _].
  specialize (H2 H5).
  specialize (H4 H6).
  contradiction.
Qed.

Lemma interior_point_in : forall D a,
  interior_point D a -> a ∈ D.
Proof.
  intros D a [δ [H1 H2]].
  apply H2. solve_R.
Qed.

Lemma unique_classification_closed : forall x a b,
  a < b -> x ∈ [a, b] -> left_endpoint [a, b] x \/ right_endpoint [a, b] x \/ interior_point [a, b] x.
Proof.
  intros x a b H1 H2. assert (x = a \/ x = b \/ a < x < b) as [H3 | [H3 | H3]] by solve_R.
  - left. apply closed_left_pt_iff; auto.
  - right. left. apply closed_right_pt_iff; auto.
  - right; right.
    apply closed_interior_iff; solve_R.
Qed.