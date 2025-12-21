From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_2_a : ⟦ lim 1 ⟧ (λ x, (1 - √x) / (1-x)) = 1/2.
Proof.
  apply limit_to_a_equiv' with (f1 := λ x, 1 / (1 + √x)) (δ := 1); try lra.
  - intros x H1. pose proof sqrt_lt_R0 x ltac:(solve_R) as H2.
    apply Rmult_eq_reg_r with (r := (1 - x) * (1 + √x)). try field_simplify; try nra.
    rewrite pow2_sqrt; solve_R. solve_R.
  - change_fun_to_expr. set (e := EDiv (EConst 1) (EAdd (EConst 1) (ESqrt EVar))). replace (1/2) with (eval e 1).
      2 : { simpl. rewrite sqrt_1. lra. } apply limit_eval_expr. repeat split; simpl; try lra. rewrite sqrt_1. lra. rewrite sqrt_1. lra.
Qed.