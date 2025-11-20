From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_18 : ∀ f a l,
  ⟦ lim a ⟧ f = l → ∃ δ M, δ > 0 /\ (∀ x, 0 < |x - a| < δ → |f x| < M).
Proof.
  intros f a l H1.
  specialize (H1 1 ltac:(solve_R)) as [δ [H2 H3]].
  exists δ, (|l| + 1). 
  split; auto.
  intros x H4.
  specialize (H3 x H4).
  solve_R.
Qed.