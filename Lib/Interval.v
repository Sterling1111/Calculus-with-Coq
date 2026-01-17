From Lib Require Import Imports Sets Notations Reals_util.
Import SetNotations.

Module IntervalNotations.

  Declare Scope interval_scope.
  Delimit Scope interval_scope with interval.
  
  Notation "[ a , b ]" := (fun x => a <= x <= b) : interval_scope.
  Notation "[ a , b )" := (fun x => a <= x < b) : interval_scope.
  Notation "( a , b ]" := (fun x => a < x <= b)  : interval_scope.
  Notation "( a , b )" := (fun x => a < x < b) : interval_scope.

  Notation "(-∞ , b )" := (fun x => x < b) : interval_scope.
  Notation "( -∞ , b ]" := (fun x => x <= b) : interval_scope.
  Notation "( a , ∞)" := (fun x => a < x) : interval_scope.
  Notation "[ a , ∞)" := (fun x => a <= x) : interval_scope.

  Notation "(-∞ , +∞)" := (Full_set _) : interval_scope.

  Open Scope interval_scope.
End IntervalNotations.

Import IntervalNotations.

Definition left_endpoint (A : Ensemble R) (a : R) :=
  exists δ, δ > 0 /\ forall x, (x ∈ [a-δ, a) -> x ∉ A) /\ (x ∈ [a, a+δ) -> x ∈ A).

Definition right_endpoint (A : Ensemble R) (a : R) :=
  exists δ, δ > 0 /\ forall x, (x ∈ (a, a+δ] -> x ∉ A) /\ (x ∈ (a-δ, a] -> x ∈ A).

Definition interior_point (A : Ensemble R) (a : R) :=
  exists δ, δ > 0 /\ forall x, x ∈ (a-δ, a+δ) -> x ∈ A.

Definition isolated_point (A : Ensemble R) (a : R) :=
  a ∈ A /\ (exists δ, δ > 0 /\ forall x, x ∈ (a-δ, a) ⋃ (a, a+δ) -> x ∉ A).

Lemma interior_full : forall x,
  interior_point (-∞, +∞) x <-> True.
Proof.
  intros x. split; intros H1.
  - auto.
  - exists 1. split; try lra. intros x0 _. apply Full_intro.
Qed.

Lemma left_full : forall x,
  left_endpoint (-∞, +∞) x <-> False.
Proof.
  intros x. split; intros H1; try contradiction.
  destruct H1 as [d [H1 H2]].
  specialize (H2 (x - d/2)).
  destruct H2 as [H2 _].
  apply H2; try apply Full_intro.
  solve_R.
Qed.

Lemma right_full : forall x,
  right_endpoint (-∞, +∞) x <-> False.
Proof.
  intros x. split; intros H1; try contradiction.
  destruct H1 as [d [H1 H2]].
  specialize (H2 (x + d/2)).
  destruct H2 as [H2 _].
  apply H2; try apply Full_intro.
  solve_R.
Qed.

Lemma interior_open : forall a b x,
  a < b -> (interior_point (a, b) x <-> a < x < b).
Proof.
  intros a b x H1. split.
  - intros [d [H2 H3]].
    specialize (H3 x). solve_R.
  - intros H2.
    exists (Rmin (x - a) (b - x)).
    split; try solve_R.
Qed.

Lemma left_open : forall a b x,
  a < b -> (left_endpoint (a, b) x <-> False).
Proof.
  intros a b x H1. split; try contradiction.
  intros [d [H2 H3]].
  assert (H4: a < x < b).
  { specialize (H3 x). solve_R. }
  set (e := Rmin (x - a) d).
  specialize (H3 (x - e/2)).
  destruct H3 as [H3 _].
  apply H3.
  - unfold e. solve_R.
  - unfold e. solve_R.
Qed.

Lemma right_open : forall a b x,
  a < b -> (right_endpoint (a, b) x <-> False).
Proof.
  intros a b x H1. split; try contradiction.
  intros [d [H2 H3]].
  assert (H4: a < x < b).
  { specialize (H3 x). solve_R. }
  set (e := Rmin (b - x) d).
  specialize (H3 (x + e/2)).
  destruct H3 as [H3 _].
  apply H3.
  - unfold e. solve_R.
  - unfold e. solve_R.
Qed.

Lemma interior_closed : forall a b x,
  a < b -> (interior_point [a, b] x <-> a < x < b).
Proof.
  intros a b x H1. split.
  - intros [d [H2 H3]].
    assert (H4: a <= x <= b).
    { specialize (H3 x). solve_R. }
    split.
    + destruct (Rtotal_order x a) as [H5 | [H5 | H5]]; try lra.
      subst. specialize (H3 (a - d/2)).
      exfalso. solve_R.
    + destruct (Rtotal_order x b) as [H5 | [H5 | H5]]; try lra.
      subst. specialize (H3 (b + d/2)).
      exfalso. solve_R.
  - intros H2.
    exists (Rmin (x - a) (b - x)).
    split; try solve_R.
Qed.

Lemma left_closed : forall a b x,
  a < b -> (left_endpoint [a, b] x <-> x = a).
Proof.
  intros a b x H1. split.
  - intros [d [H2 H3]].
    assert (H4: a <= x <= b).
    { specialize (H3 x). solve_R. }
    destruct H4 as [H4 H5].
    destruct (Rtotal_order x a) as [H6 | [H6 | H6]]; try lra.
    assert (H7: a < x <= b) by lra.
    set (e := Rmin (x - a) d).
    specialize (H3 (x - e/2)).
    destruct H3 as [H3 _].
    exfalso. apply H3.
    + unfold e; solve_R.
    + unfold e; solve_R.
  - intros H2. subst.
    exists (b - a).
    split; try lra.
    intros x0. split; solve_R.
Qed.

Lemma right_closed : forall a b x,
  a < b -> (right_endpoint [a, b] x <-> x = b).
Proof.
  intros a b x H1. split.
  - intros [d [H2 H3]].
    assert (H4: a <= x <= b).
    { specialize (H3 x). solve_R. }
    destruct H4 as [H4 H5].
    destruct (Rtotal_order x b) as [H6 | [H6 | H6]]; try lra.
    assert (H7: a <= x < b) by lra.
    set (e := Rmin (b - x) d).
    specialize (H3 (x + e/2)).
    destruct H3 as [H3 _].
    exfalso. apply H3.
    + unfold e; solve_R.
    + unfold e; solve_R.
  - intros H2. subst.
    exists (b - a).
    split; try lra.
    intros x0. split; solve_R.
Qed.

Lemma interior_ropen : forall a b x,
  a < b -> (interior_point [a, b) x <-> a < x < b).
Proof.
  intros a b x H1. split.
  - intros [d [H2 H3]].
    assert (H4: a <= x < b).
    { specialize (H3 x). solve_R. }
    split; try lra.
    destruct (Rtotal_order x a) as [H5 | [H5 | H5]]; try lra.
    subst. specialize (H3 (a - d/2)).
    exfalso. solve_R.
  - intros H2.
    exists (Rmin (x - a) (b - x)).
    split; try solve_R.
Qed.

Lemma left_ropen : forall a b x,
  a < b -> (left_endpoint [a, b) x <-> x = a).
Proof.
  intros a b x H1. split.
  - intros [d [H2 H3]].
    assert (H4: a <= x < b).
    { specialize (H3 x). solve_R. }
    destruct (Rtotal_order x a) as [H6 | [H6 | H6]]; try lra.
    assert (H7: a < x < b) by lra.
    set (e := Rmin (x - a) d).
    specialize (H3 (x - e/2)).
    destruct H3 as [H3 _].
    exfalso. apply H3; unfold e; solve_R.
  - intros H2. subst.
    exists (b - a). split; try lra.
    intros x0. split; solve_R.
Qed.

Lemma right_ropen : forall a b x,
  a < b -> (right_endpoint [a, b) x <-> False).
Proof.
  intros a b x H1. split; try contradiction.
  intros [d [H2 H3]].
  assert (H4: a <= x < b).
  { specialize (H3 x). solve_R. }
  set (e := Rmin (b - x) d).
  specialize (H3 (x + e/2)).
  destruct H3 as [H3 _].
  apply H3; unfold e; solve_R.
Qed.

Lemma interior_lopen : forall a b x,
  a < b -> (interior_point (a, b] x <-> a < x < b).
Proof.
  intros a b x H1. split.
  - intros [d [H2 H3]].
    assert (H4: a < x <= b).
    { specialize (H3 x). solve_R. }
    split; try lra.
    destruct (Rtotal_order x b) as [H5 | [H5 | H5]]; try lra.
    subst. specialize (H3 (b + d/2)).
    exfalso. solve_R.
  - intros H2.
    exists (Rmin (x - a) (b - x)).
    split; try solve_R.
Qed.

Lemma left_lopen : forall a b x,
  a < b -> (left_endpoint (a, b] x <-> False).
Proof.
  intros a b x H1. split; try contradiction.
  intros [d [H2 H3]].
  assert (H4: a < x <= b).
  { specialize (H3 x). solve_R. }
  set (e := Rmin (x - a) d).
  specialize (H3 (x - e/2)).
  destruct H3 as [H3 _].
  apply H3; unfold e; solve_R.
Qed.

Lemma right_lopen : forall a b x,
  a < b -> (right_endpoint (a, b] x <-> x = b).
Proof.
  intros a b x H1. split.
  - intros [d [H2 H3]].
    assert (H4: a < x <= b).
    { specialize (H3 x). solve_R. }
    destruct (Rtotal_order x b) as [H6 | [H6 | H6]]; try lra.
    assert (H7: a < x < b) by lra.
    set (e := Rmin (b - x) d).
    specialize (H3 (x + e/2)).
    destruct H3 as [H3 _].
    exfalso. apply H3; unfold e; solve_R.
  - intros H2. subst.
    exists (b - a). split; try lra.
    intros x0. split; solve_R.
Qed.

Lemma interior_not_left : forall D x,
  interior_point D x -> left_endpoint D x -> False.
Proof.
  intros D x H1 H2.
  destruct H1 as [d1 [H3 H4]].
  destruct H2 as [d2 [H5 H6]].
  set (d3 := Rmin d1 d2).
  set (x0 := x - d3 / 2).
  assert (H7 : x0 ∈ (x - d1, x + d1)).
  { unfold x0, d3; solve_R. }
  assert (H8 : x0 ∈ [x - d2, x)).
  { unfold x0, d3; solve_R. }
  specialize (H4 x0 H7).
  specialize (H6 x0). destruct H6 as [H6 _].
  specialize (H6 H8).
  contradiction.
Qed.

Lemma interior_not_right : forall D x,
  interior_point D x -> right_endpoint D x -> False.
Proof.
  intros D x H1 H2.
  destruct H1 as [d1 [H3 H4]].
  destruct H2 as [d2 [H5 H6]].
  set (d3 := Rmin d1 d2).
  set (x0 := x + d3 / 2).
  assert (H7 : x0 ∈ (x - d1, x + d1)).
  { unfold x0, d3; solve_R. }
  assert (H8 : x0 ∈ (x, x + d2]).
  { unfold x0, d3; solve_R. }
  specialize (H4 x0 H7).
  specialize (H6 x0). destruct H6 as [H6 _].
  specialize (H6 H8).
  contradiction.
Qed.

Lemma left_not_right : forall D x,
  left_endpoint D x -> right_endpoint D x -> False.
Proof.
  intros D x H1 H2.
  destruct H1 as [d1 [H3 H4]].
  destruct H2 as [d2 [H5 H6]].
  set (d3 := Rmin d1 d2).
  set (x0 := x + d3 / 2).
  assert (H7 : x0 ∈ [x, x + d1)).
  { unfold x0, d3; solve_R. }
  assert (H8 : x0 ∈ (x, x + d2]).
  { unfold x0, d3; solve_R. }
  specialize (H4 x0) as [_ H4].
  specialize (H4 H7).
  specialize (H6 x0) as [H6 _].
  specialize (H6 H8).
  contradiction.
Qed.

Create HintDb interval_db.

Hint Rewrite 
  interior_full left_full right_full
  interior_open left_open right_open
  interior_closed left_closed right_closed
  interior_ropen left_ropen right_ropen
  interior_lopen left_lopen right_lopen : interval_db.

Ltac auto_interval :=
  intros;
  repeat match goal with
  | [ H : interior_point _ _ /\ _ |- _ ] => destruct H
  | [ H : left_endpoint _ _ /\ _ |- _ ] => destruct H
  | [ H : right_endpoint _ _ /\ _ |- _ ] => destruct H
  end;
  try match goal with
  | [ H1 : interior_point ?D ?x, H2 : left_endpoint ?D ?x |- _ ] =>
      exfalso; apply (interior_not_left D x H1 H2)
  | [ H1 : interior_point ?D ?x, H2 : right_endpoint ?D ?x |- _ ] =>
      exfalso; apply (interior_not_right D x H1 H2)
  | [ H1 : left_endpoint ?D ?x, H2 : right_endpoint ?D ?x |- _ ] =>
      exfalso; apply (left_not_right D x H1 H2)
  end;
  autorewrite with interval_db in *;
  try match goal with
  | [ H : _ < _ |- _ ] => idtac
  end;
  try solve_R.

Lemma classify_closed : forall x a b,
  a < b -> x ∈ [a, b] -> left_endpoint [a, b] x \/ right_endpoint [a, b] x \/ interior_point [a, b] x.
Proof.
  intros x a b H1 H2. assert (x = a \/ x = b \/ a < x < b) as [H3 | [H3 | H3]] by solve_R.
  - left. auto_interval.
  - right. left. auto_interval.
  - right; right. auto_interval.
Qed.