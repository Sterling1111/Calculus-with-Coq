Require Import Imports Limit Reals_util.
Import LimitNotations.

Lemma lemma_5_1_i : ⟦ lim 1 ⟧ (λ x, (x^2 - 1) / (x + 1)) = 0.
Proof. solve_lim. Qed.

Lemma lemma_5_1_ii : ⟦ lim 2 ⟧ (λ x, (x^3 - 8) / (x - 2)) = 12.
Proof. apply limit_to_a_equiv with (f1 := λ x, x^2 + 2 * x + 4); solve_lim. Qed.

Lemma lemma_5_1_iii : ⟦ lim 3 ⟧ (λ x, (x^3 - 8) / (x - 2)) = 19.
Proof. solve_lim. Qed.

Lemma lemma_5_1_iv : forall y n, ⟦ lim y ⟧ (λ x, (x^n - y^n) / (x - y)) = (INR n) * y^(n - 1).
Proof.
  intros y n. induction n as [| k IH].
  - simpl. apply limit_to_a_equiv with (f1 := λ x, 0); solve_lim.
  - replace (S k - 1)%nat with k by lia. apply limit_to_a_equiv with (f1 := λ x, x^k + y * ((x^k - y^k) / (x - y))); solve_R.
    replace ((INR k + 1) * y ^ k) with (y^k + (INR k) * y^k) by solve_R. apply limit_plus; try solve_lim.
    assert (k = 0 \/ k <> 0)%nat as [H1 | H1] by lia.
    -- rewrite H1. simpl. field_simplify. apply limit_to_a_equiv with (f1 := λ _, 0); solve_lim.
    -- apply (limit_mult (λ x, y) _ _ y) in IH; try solve_lim.
       replace (y * (INR k * y ^ (k - 1))) with ((INR k) * y ^ k) in IH.
       2 : { pose proof tech_pow_Rmult y (k - 1) as H2. replace (S (k - 1))%nat with k in H2 by lia. solve_R. }
       auto.
Qed.

Lemma lemma_5_1_v : forall x n, ⟦ lim x ⟧ (λ y, (x^n - y^n) / (x - y)) = (INR n) * x^(n - 1).
Proof.
  intros x n. apply limit_to_a_equiv with (f1 := λ y : R, (y ^ n - x ^ n) / (y - x)).
  - intros y Hy. field; lra.
  - apply lemma_5_1_iv.
Qed.

Lemma lemma_5_vi : forall a, 
  ⟦ lim a ⟧ (λ x, sqrt 
Proof.
Qed.