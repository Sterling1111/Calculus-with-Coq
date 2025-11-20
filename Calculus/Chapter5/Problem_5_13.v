From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_13 : ∀ f g h a L,
  (∀ x, f x ≤ g x ≤ h x) → ⟦ lim a ⟧ f = L → ⟦ lim a ⟧ h = L → ⟦ lim a ⟧ g = L.
Proof.
  intros f g h a L H1 H2 H3 ε H4.
  specialize (H2 ε H4) as [δ1 [H5 H6]].
  specialize (H3 ε H4) as [δ2 [H7 H8]].
  exists (Rmin δ1 δ2). split; [ solve_R | intros x H9 ].
  specialize (H6 x ltac:(solve_R)).
  specialize (H8 x ltac:(solve_R)).
  specialize (H1 x).
  solve_R.
Qed.