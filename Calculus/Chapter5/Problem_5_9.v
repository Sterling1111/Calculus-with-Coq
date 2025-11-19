From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_9 : ∀ f a L1 L2,
  ⟦ lim a ⟧ f = L1 ->  ⟦ lim 0 ⟧ (λ h, f(a + h)) = L2 -> L1 = L2.
Proof.
  intros f a L1 L2 H1 H2. apply cond_eq. intros ε H3. specialize (H1 (ε/2) ltac:(lra)) as [δ1 [H1 H4]].
  specialize (H2 (ε/2) ltac:(lra)) as [δ2 [H2 H5]]. set (δ := Rmin δ1 δ2).
  specialize (H4 (a + δ / 2) ltac:(unfold δ; solve_R)).
  specialize (H5 (δ / 2) ltac:(unfold δ; solve_R)).
  solve_R.
Qed.