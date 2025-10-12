Require Import Limit Imports Notations Reals_util.
Import LimitNotations.

Lemma lemma_5_16_a : forall a f l,
  ⟦ lim a ⟧ f = l -> ⟦ lim a ⟧ (λ x, |f x|) = |l|.
Proof.
  intros a f l H1 ε H2. specialize (H1 ε H2) as [δ [H1 H3]].
  exists δ. split; auto. intros x H4. specialize (H3 x H4). solve_R.
Qed.

Lemma lemma_5_16_b_1 : forall a f g l m,
  ⟦ lim a ⟧ f = l -> ⟦ lim a ⟧ g = m -> ⟦ lim a ⟧ (λ x, Rmax (f x) (g x)) = Rmax l m.
Proof.
  intros a f g l m H1 H2 ε H3.
  specialize (H1 ε H3) as [δ1 [H4 H5]]. specialize (H2 ε H3) as [δ2 [H6 H7]].
  exists (Rmin δ1 δ2). split; [solve_R | ].
  intros x H8. specialize (H5 x ltac:(solve_R)). specialize (H7 x ltac:(solve_R)).
  solve_R.
Qed.

Lemma lemma_5_16_b_2 : forall a f g l m,
  ⟦ lim a ⟧ f = l -> ⟦ lim a ⟧ g = m -> ⟦ lim a ⟧ (λ x, Rmin (f x) (g x)) = Rmin l m.
Proof.
  intros a f g l m H1 H2 ε H3.
  specialize (H1 ε H3) as [δ1 [H4 H5]]. specialize (H2 ε H3) as [δ2 [H6 H7]].
  exists (Rmin δ1 δ2). split; [solve_R | ].
  intros x H8. specialize (H5 x ltac:(solve_R)). specialize (H7 x ltac:(solve_R)).
  solve_R.
Qed.