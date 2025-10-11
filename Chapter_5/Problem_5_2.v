Require Import Imports Limit Reals_util Notations.
Import LimitNotations.

Lemma lemma_5_2_a : ⟦ lim 1 ⟧ (λ x, (1 - √x) / (1-x)) = 1/2.
Proof.
  apply limit_to_a_equiv with (f2 := λ x, (1 - √x) / (1 - x)) (a := 1) (l := 1/2).
Qed.