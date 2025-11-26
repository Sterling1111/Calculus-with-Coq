From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_38_b :  ⟦ lim 0⁺ ⟧ (λ x : ℝ, 1 / x) = ∞.
Proof.
  intros M. exists (1 / (|M| + 1)). split.
  - apply Rdiv_pos_pos; solve_R.
  - intros x [H1 H2]. rewrite Rminus_0_r in *. apply Rmult_lt_reg_l with (r := x); auto.
    field_simplify; try lra. apply Rmult_lt_compat_r with (r := |M| + 1) in H2; solve_R.
    field_simplify in H2; solve_R.
Qed.

