From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_7 : ∃ (f : R -> R) (l a : R) (ε δ : R), 
  ε > 0 /\ δ > 0 /\
  (∀ x, 0 < |x - a| < δ -> |f x - l| < ε) /\
  ¬ (∀ x, 0 < |x - a| < δ/2 -> |f x - l| < ε/2).
Proof.
  exists (fun x => √|x|), 0, 0, (1/2), (1/4); repeat split; try lra.
  - intros x [H1 H2].
    assert (H3: √(|x|) < 1 / 2).
    {
      replace (1 / 2) with (√(1 / 4)).
      - apply sqrt_lt_1_alt. solve_R.
      - replace (1 / 4) with ((1 / 2) * (1 / 2)) by lra. apply sqrt_square; lra.
    }
    rewrite Rminus_0_r.
    apply Rabs_def1; auto.
    assert (H5: 0 <= √(|x|)) by apply sqrt_pos; lra.
  - intro H1. specialize (H1 (1/16) ltac:(solve_R)).
    rewrite Rminus_0_r in H1. 
    replace (|(1 / 16)|) with ((1 / 4) * (1 / 4)) in H1 by solve_R.
    rewrite sqrt_square in H1; solve_R.
Qed.