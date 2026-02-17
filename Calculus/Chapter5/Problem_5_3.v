From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_3_i : ⟦ lim 0 ⟧ (λ x, x * (3 - cos (x^2))) = 0.
Admitted.

Lemma lemma_5_3_ii : ⟦ lim 2 ⟧ (λ x, x^2 + 5 * x - 2) = 12.
Admitted.

Lemma lemma_5_3_iii : ⟦ lim 1 ⟧ (λ x, 100 / x) = 100.
Admitted.

Lemma lemma_5_3_iv (a : R) : ⟦ lim a ⟧ (λ x, x^4) = a^4.
Admitted.

Lemma lemma_5_3_v : ⟦ lim 1 ⟧ (λ x, x^4 + 1 / x) = 2.
Admitted.

Lemma lemma_5_3_vi : ⟦ lim 0 ⟧ (λ x, x / (2 - (sin x)^2)) = 0.
Admitted.

Lemma lemma_5_3_vii : ⟦ lim 0 ⟧ (λ x, sqrt (Rabs x)) = 0.
Admitted.

Lemma lemma_5_3_viii : ⟦ lim 1 ⟧ (λ x, sqrt x) = 1.
Admitted.