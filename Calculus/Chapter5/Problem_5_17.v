Require Import Limit Imports Notations Reals_util.
Import LimitNotations.

Lemma lemma_5_17_a : forall l, 
  ~ ⟦ lim 0 ⟧ (λ x, 1 / x) = l.
Proof.
  intros l H1. specialize (H1 1) as [δ [H2 H3]]; try lra.
  specialize (H3 (Rmin (δ/2) (1/2)) ltac:(solve_R)).
  assert (H4 : forall a b c, a > 0 -> 0 < b < 1 -> 0 < c < b -> a / b < a / c).
  {
    intros a b c H4 H5 H6. apply Rmult_lt_reg_l with (r := b); 
    apply Rmult_lt_reg_l with (r := c); try nra. 
    field_simplify; try lra. apply Rmult_lt_compat_r; try lra. 
  }
  assert ((δ / 2) < (1/2) \/ (δ / 2) >= (1/2)) as [H5 | H5] by lra.
  - specialize (H4 1 (1/2) (δ/2) ltac:(lra) ltac:(solve_R) (ltac:(solve_R))) as H6.
    replace (1 / (1 / 2)) with 2 in * by lra.
    solve_R.
  admit.
Admitted.