From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_11 : ∀ f g a L δ,
  δ > 0 → (∀ x, 0 < |x - a| < δ → f x = g x) → 
    ⟦ lim a ⟧ f = L → ⟦ lim a ⟧ g = L.
Proof.
  intros f g a L δ1 H1 H2 H3 ε H4. specialize (H3 ε H4) as [δ2 [H5 H6]].
  set (δ := Rmin δ1 δ2). exists δ. split; [ solve_R | intros x H7 ].
  specialize (H6 x ltac:(unfold δ in *; solve_R)).
  specialize (H2 x ltac:(unfold δ in *; solve_R)).
  solve_R.
Qed.