From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_2_i : ⟦ lim 1 ⟧ (λ x, (1 - √x) / (1-x)) = 1/2.
Proof.
  apply limit_eq with (f1 := λ x, 1 / (1 + √x)).
  - exists 1. split; try lra. intros x H1. pose proof sqrt_lt_R0 x ltac:(solve_R) as H2.
    apply Rmult_eq_reg_r with (r := (1 - x) * (1 + √x)). 2 : { solve_R. } field_simplify; try solve [solve_R].
    rewrite pow2_sqrt; solve_R.
  - auto_limit; simpl; rewrite sqrt_1; lra.
Qed.

Lemma lemma_5_2_ii : ⟦ lim 0 ⟧ (λ x, (1 - √(1 - x^2))/ x) = 0.
Proof.
  apply limit_eq with (f1 := λ x, x / (1 + √(1 - x^2))).
  - exists 1. split; try lra. intros x H1. pose proof sqrt_lt_R0 (1 - x^2) ltac:(solve_R) as H2.
    apply Rmult_eq_reg_r with (r := x * (1 + √(1 - x^2))). 2 : { intros H3; solve_R. } field_simplify; [| solve_R | lra ].
    rewrite pow2_sqrt; solve_R.
  - auto_limit; simpl; rewrite Rmult_0_l, Rminus_0_r, sqrt_1; lra.
Qed.

Lemma lemma_5_2_iii : ⟦ lim 0 ⟧ (λ x, (1 - √(1 - x^2))/ x^2) = 1/2.
Proof.
  apply limit_eq with (f1 := λ x, 1 / (1 + √(1 - x^2))).
  - exists 1. split; try lra. intros x H1. pose proof sqrt_lt_R0 (1 - x^2) ltac:(solve_R) as H2.
    apply Rmult_eq_reg_r with (r := x^2 * (1 + √(1 - x^2))). 2 : { intros H3; solve_R. } field_simplify; [| solve_R | lra ].
    rewrite pow2_sqrt; solve_R.
  - auto_limit; simpl; rewrite Rmult_0_l, Rminus_0_r, sqrt_1; lra.
Qed.