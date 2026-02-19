From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_15 : ∀ f a ε,
  ε > 0 -> continuous_at f a -> ∃ δ, δ > 0 ∧ ∀ x y, |x - a| < δ → |y - a| < δ → |f x - f y| < ε.
Proof.
  intros f a ε H1 H2. specialize (H2 (ε/2) ltac:(lra)) as [δ [H2 H3]]. exists δ. split; [ solve_R | ].
  intros x y H4 H5. pose proof classic (x = a) as [H6 | H6]; pose proof classic (y = a) as [H7 | H7]; subst.
  - solve_R.
  - specialize (H3 y ltac:(solve_R)). solve_R.
  - specialize (H3 x ltac:(solve_R)). solve_R.
  - specialize (H3 x ltac:(solve_R)) as H8. specialize (H3 y ltac:(solve_R)). solve_R. 
Qed.