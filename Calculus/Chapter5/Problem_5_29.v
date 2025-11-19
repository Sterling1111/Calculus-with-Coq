From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_29 : ∀ f a L,
  ⟦ lim a⁺ ⟧ f = L → ⟦ lim a⁻ ⟧ f = L → ⟦ lim a ⟧ f = L.
Proof.
  intros f a L H1 H2 ε H3.    
  specialize (H1 ε H3) as [δ1 [H4 H5]].
  specialize (H2 ε H3) as [δ2 [H6 H7]].
  exists (Rmin δ1 δ2). split; [ solve_R | intros x H8 ].
  specialize (H5 x). specialize (H7 x). solve_R.
Qed.

Lemma lemma_5_29' : ∀ f a L,
  ⟦ lim a⁺ ⟧ f = L → ⟦ lim a⁻ ⟧ f = L → ⟦ lim a ⟧ f = L.
Proof.
  intros f a L H1 H2. apply left_right_iff; auto.
Qed.