From Stdlib Require Reals Lra.
From Lib Require Import Imports Tactics Limit Derivative Integral Continuity Reals_util.
Import LimitNotations DerivativeNotations.

Lemma limit_compat : forall f a L,
  ⟦ lim a ⟧ f = L <-> limit1_in f (fun x => x <> a) L a.
Proof.
  split; intros H eps Heps.
  - unfold limit in H. destruct (H eps Heps) as [delta [Hdelta H1]].
    unfold limit1_in. unfold limit_in.
    exists delta; split; auto.
    intros x [Hx H2]. simpl in H2.
    apply H1. split; [| auto]. apply Rabs_pos_lt. lra.
  - unfold limit1_in, limit_in in H. destruct (H eps Heps) as [delta [Hdelta H1]].
    unfold limit. exists delta; split; auto.
    intros x [H2 H3]. apply H1. split; auto.
    intro C; subst. replace (a - a) with 0 in H2 by lra. rewrite Rabs_R0 in H2; lra.
Qed.

Lemma derivative_compat : forall f f' a,
  ⟦ der a ⟧ f = f' <-> derivable_pt_lim f a (f' a).
Proof.
  split.
  - intros H eps Heps. unfold derivative_at, limit in H.
    destruct (H eps Heps) as [delta [Hdelta H1]].
    exists (mkposreal delta Hdelta). intros h Hh1 Hh2.
    apply H1. split; auto.
    + apply Rabs_pos_lt; lra.
    + replace (h - 0) with h by lra; exact Hh2.
  - intros H. unfold derivative_at, limit. intros eps Heps.
    destruct (H eps Heps) as [delta H1].
    exists delta. split. apply cond_pos.
    intros h [H2 H3]. apply H1.
    + intro C; subst; replace (0 - 0) with 0 in H2 by lra; rewrite Rabs_R0 in H2; lra.
    + replace h with (h - 0) by lra; exact H3.
Qed.

Lemma continuous_compat : forall f a,
  continuous_at f a <-> continuity_pt f a.
Proof.
  split; intros H.
  - unfold continuity_pt, continue_in. unfold D_x, no_cond.
    assert (H_eq : (fun x => True /\ a <> x) = (fun x => x <> a)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition. }
    rewrite H_eq. apply limit_compat. apply H.
  - unfold continuity_pt, continue_in in H. unfold D_x, no_cond in H.
    assert (H_eq : (fun x => True /\ a <> x) = (fun x => x <> a)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition. }
    rewrite H_eq in H. apply limit_compat in H. apply H.
Qed.

Lemma right_limit_compat : forall f a L,
  ⟦ lim a⁺ ⟧ f = L <-> limit1_in f (fun x => a < x) L a.
Proof.
  split; intros H eps Heps.
  - unfold right_limit in H. destruct (H eps Heps) as [delta [Hdelta H1]].
    unfold limit1_in, limit_in.
    exists delta; split; auto.
    intros x [Hx H2]. apply H1. simpl in H2.
    unfold Rdist in *; rewrite Rabs_pos_eq in H2; lra.
  - unfold limit1_in, limit_in in H. destruct (H eps Heps) as [delta [Hdelta H1]].
    unfold right_limit. exists delta; split; auto.
    intros x H2. apply H1. split; auto. lra.
    simpl. unfold Rdist in *; rewrite Rabs_pos_eq; lra.
Qed.

Lemma left_limit_compat : forall f a L,
  ⟦ lim a⁻ ⟧ f = L <-> limit1_in f (fun x => x < a) L a.
Proof.
  split; intros H eps Heps.
  - unfold left_limit in H. destruct (H eps Heps) as [delta [Hdelta H1]].
    unfold limit1_in, limit_in.
    exists delta; split; auto.
    intros x [Hx H2]. apply H1. simpl in H2.
    unfold Rdist in *; rewrite Rabs_left in H2; lra.
  - unfold limit1_in, limit_in in H. destruct (H eps Heps) as [delta [Hdelta H1]].
    unfold left_limit. exists delta; split; auto.
    intros x H2. apply H1. split; auto. lra.
    simpl. unfold Rdist in *; rewrite Rabs_left; lra.
Qed.

Lemma right_continuous_compat : forall f a,
  continuous_at_right f a <-> continue_in f (fun x => a <= x) a.
Proof.
  split; intros H.
  - unfold continuous_at_right in H. unfold continue_in.
    assert (H_eq : (fun x => a <= x /\ a <> x) = (fun x => a < x)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition lra. }
    unfold D_x. rewrite H_eq.
    apply right_limit_compat. apply H.
  - unfold continuous_at_right. unfold continue_in, D_x in H.
    assert (H_eq : (fun x => a <= x /\ a <> x) = (fun x => a < x)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition lra. }
    rewrite H_eq in H.
    apply right_limit_compat in H. apply H.
Qed.

Lemma left_continuous_compat : forall f a,
  continuous_at_left f a <-> continue_in f (fun x => x <= a) a.
Proof.
  split; intros H.
  - unfold continuous_at_left in H. unfold continue_in.
    assert (H_eq : (fun x => x <= a /\ a <> x) = (fun x => x < a)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition lra. }
    unfold D_x. rewrite H_eq.
    apply left_limit_compat. apply H.
  - unfold continuous_at_left. unfold continue_in, D_x in H.
    assert (H_eq : (fun x => x <= a /\ a <> x) = (fun x => x < a)).
    { extensionality x. apply propositional_extensionality. split; intros; intuition lra. }
    rewrite H_eq in H.
    apply left_limit_compat in H. apply H.
Qed.

Lemma derivative_all_compat : forall f f',
  ⟦ der ⟧ f = f' <-> (forall x, derivable_pt_lim f x (f' x)).
Proof.
  split; intros H x; apply derivative_compat; apply H.
Qed.

Lemma continuous_all_compat : forall f,
  continuous f <-> (forall x, continuity_pt f x).
Proof.
  split; intros H x; apply continuous_compat; apply H.
Qed.

Lemma Riemann_implies_integrable_on : forall f a b,
  a <= b -> Riemann_integrable f a b -> integrable_on a b f.
Proof.
Admitted.

Lemma integrable_on_implies_Riemann : forall f a b,
  a <= b -> integrable_on a b f -> 
  {pr : Riemann_integrable f a b | True}.
Proof.
Admitted.

Lemma definite_integral_compat : forall f a b pr,
  a <= b ->
  definite_integral a b f = RiemannInt (f:=f) (a:=a) (b:=b) pr.
Proof.
  intros f a b pr Hab.
  unfold definite_integral. destruct (Rle_dec a b) as [H1 | H1]; try lra.
  destruct (integrable_dec a b f) as [H2 | H2].
  - unfold RiemannInt.
Admitted.
