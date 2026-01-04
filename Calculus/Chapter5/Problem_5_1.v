From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_1_i : ⟦ lim 1 ⟧ (λ x, (x^2 - 1) / (x + 1)) = 0.
Proof. auto_limit. Qed.

Lemma lemma_5_1_ii : ⟦ lim 2 ⟧ (λ x, (x^3 - 8) / (x - 2)) = 12.
Proof. apply limit_eq with (f1 := λ x, x^2 + 2 * x + 4). exists 1. split; try lra.
  intros x H1. solve_R. auto_limit.
Qed.

Lemma lemma_5_1_iii : ⟦ lim 3 ⟧ (λ x, (x^3 - 8) / (x - 2)) = 19.
Proof. auto_limit. Qed.

Lemma lemma_5_1_iv : forall y n, ⟦ lim y ⟧ (λ x, (x^n - y^n) / (x - y)) = (INR n) * y^(n - 1).
Proof.
  intros y n. induction n as [| k IH].
  - simpl. apply limit_eq with (f1 := λ x, 0); [ | auto_limit ].
    exists 1. split; try lra. intros x H1. rewrite Rminus_diag, Rdiv_0_l; auto.
  - replace (S k - 1)%nat with k by lia.
    apply limit_eq with (f1 := λ x, x^k + y * ((x^k - y^k) / (x - y))).
    + exists 1. split; try lra. intros x H1. solve_R.
    + replace (S k * y ^ k) with (y^k + y * (INR k * y ^ (k - 1))) by admit.
      apply limit_plus.
      * apply limit_pow; apply limit_id.
      * apply limit_mul; [apply limit_const | exact IH].
Admitted.

Lemma lemma_5_1_v : forall x n, ⟦ lim x ⟧ (λ y, (x^n - y^n) / (x - y)) = (INR n) * x^(n - 1).
Proof.
  intros x n. apply limit_eq with (f1 := λ y : R, (y ^ n - x ^ n) / (y - x)).
  - exists 1. split; try lra. intros y Hy. solve_R.
  - apply lemma_5_1_iv.
Qed.

Lemma lemma_5_vi : forall a, a > 0 -> ⟦ lim 0 ⟧ (λ h, (√(a + h) - √a) / h) = 1 / (2 * √a).
Proof.
  intros a H1. apply limit_eq with (f1 := λ h, 1 / (√(a + h) + √a)).
  - exists (a/2). split; try lra. intros h [H2 H3]. assert (√a > 0 /\ √(a + h) > 0) as [H4 H5] by (split; apply sqrt_lt_R0; solve_R).
    apply Rmult_eq_reg_r with (r := h * (√(a + h) + √a)). 2 : { solve_R. }
    field_simplify; try solve [solve_R].
    repeat rewrite pow2_sqrt; solve_R.
  - apply limit_div.
    -- apply limit_const.
    -- replace (2 * √a) with (√a + √a) by lra. apply limit_plus. 2 : { apply limit_const. }
       apply limit_continuous_comp with (f := sqrt) (g := λ x, a + x); solve_lim.
    -- pose proof sqrt_lt_R0 a H1 as H2. lra.
Qed.