Require Import Imports Limit Reals_util Notations.
Import LimitNotations.

Lemma lemma_5_12_a : ∀ f g a L1 L2,
  (∀ x, f x <= g x) -> ⟦ lim a ⟧ f = L1 -> ⟦ lim a ⟧ g = L2 -> L1 <= L2.
Proof.
  intros f g a L1 L2 H1 H2 H3. pose proof Rle_or_gt L1 L2 as [H4 | H4]; auto.
  exfalso. set (ε := (L1 - L2)/2). assert (H5 : ε > 0) by (unfold ε; lra).
  specialize (H2 ε H5) as [δ1 [H6 H7]]. specialize (H3 ε H5) as [δ2 [H8 H9]].
  set (δ := (Rmin δ1 δ2) / 2). set (x := δ + a).
  specialize (H7 x ltac:(unfold x, δ; solve_R)). specialize (H9 x ltac:(unfold x, δ; solve_R)).
  specialize (H1 x). unfold ε in *; solve_R. 
Qed.

Print lemma_5_12_a.