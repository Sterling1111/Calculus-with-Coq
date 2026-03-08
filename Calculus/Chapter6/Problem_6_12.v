From Calculus.Chapter6 Require Import Prelude.
From Lib Require Import Tactics.

Lemma lemma_6_12_a : forall f g a l,
  continuous_at f l -> ⟦ lim a ⟧ g = l ->
  ⟦ lim a ⟧ (fun x => f (g x)) = f l.
Proof.
  intros f g a l H1 H2. apply limit_continuous_comp with (L := l).
  - exact H2.
  - exact H1.
Qed.

Lemma lemma_6_12_b :
  exists f g a l, ⟦ lim a ⟧ g = l /\ 
                  ~ (⟦ lim a ⟧ (fun x => f (g x)) = f l).
Proof.
  exists (fun x => if Req_EM_T x 0 then 1 else 0), (fun x => x), 0, 0.
  split.
  - apply limit_id.
  - intros H1. assert (H2 : (if Req_EM_T 0 0 then 1 else 0) = 1) by (destruct (Req_EM_T 0 0); lra).
    rewrite H2 in H1. destruct (H1 (1/2) ltac:(lra)) as [δ [H3 H4]].
    specialize (H4 (δ / 2)). assert (0 < |δ / 2 - 0| < δ) as H by solve_R.
    apply H4 in H. assert (H6 : (if Req_EM_T (δ / 2) 0 then 1 else 0) = 0).
    { destruct (Req_EM_T (δ / 2) 0); lra. }
    rewrite H6 in H. solve_R.
Qed.
