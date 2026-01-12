From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_21_b : ∀ g h M,
  (∀ x, |h x| <= M) → ⟦ lim 0 ⟧ g = 0 → ⟦ lim 0 ⟧ (g ⋅ h) = 0.
Proof.
  intros g h M H1 H2 ε H3.
  specialize (H2 (ε / (|M| + 1)) ltac:(apply Rdiv_pos_pos; solve_R)) as [δ [H4 H5]].
  exists δ. split; [ solve_R | intros x H6 ]. 
  specialize (H5 x ltac:(solve_R)). specialize (H1 x). rewrite Rminus_0_r in H5.
  assert (M * (ε / ((|M|) + 1)) < ε) as H7.
  { pose proof Rdiv_lt_1 M (|M| + 1) ltac:(solve_R). solve_R. }
  solve_R.
Qed.