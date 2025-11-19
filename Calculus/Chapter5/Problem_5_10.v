From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_10_a : forall a f l,
	⟦ lim a ⟧ f = l <-> ⟦ lim a ⟧ (λ x, f x - l) = 0.
Proof.
  intros a f l. split; intros H1 ε H2.
  - specialize (H1 ε H2) as [δ [H3 H4]].
    exists δ. split; auto. intros x H5. specialize (H4 x H5). solve_R.  
  - specialize (H1 ε H2) as [δ [H3 H4]].
    exists δ. split; auto. intros x H5. specialize (H4 x H5). solve_R.
Qed.

Lemma lemma_5_10_b : forall a f L1 L2,
  ⟦ lim 0 ⟧ f = L1 -> ⟦ lim a ⟧ (λ x, f (x - a)) = L2 -> L1 = L2.
Proof.
  intros a f L1 L2 H1 H2. apply cond_eq. intros ε H3.
  specialize (H1 (ε/2) ltac:(solve_R)) as [δ1 [H4 H5]].
  specialize (H2 (ε/2) ltac:(solve_R)) as [δ2 [H6 H7]].
  set (δ := (Rmin δ1 δ2) / 2).
  specialize (H5 δ ltac:(unfold δ in *; solve_R)).
  specialize (H7 (a + δ) ltac:(unfold δ in *; solve_R)).
  replace (a + δ - a) with δ in H7 by (solve_R).
  solve_R.
Qed.

Lemma lemma_5_10_c : forall f L1 L2,
  ⟦ lim 0 ⟧ f = L1 -> ⟦ lim 0 ⟧ (λ x, f (x^3)) = L2 -> L1 = L2.
Proof.
  intros f L1 L2 H1 H2. apply cond_eq. intros ε H3. specialize (H1 (ε/2) ltac:(solve_R)) as [δ1 [H4 H5]].
  specialize (H2 (ε/2) ltac:(solve_R)) as [δ2 [H6 H7]].
  set (δ := (Rmin δ1 δ2) / 2).
  assert (H0 : 0 < (|((δ^3) - 0)|) < δ1) by admit.
  specialize (H5 (δ^3) H0).
  specialize (H7 (δ) ltac:(unfold δ in *; solve_R)).
  solve_R.
Admitted.