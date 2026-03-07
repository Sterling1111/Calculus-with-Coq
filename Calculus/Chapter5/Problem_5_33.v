From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_33_i : ⟦ lim ∞ ⟧ (fun x => (x + (sin x)^3) / (5 * x + 6)) = 1/5. Proof. Admitted.
Lemma lemma_5_33_ii : ⟦ lim ∞ ⟧ (fun x => x * sin x / (x^2 + 5)) = 0. Proof. Admitted.
Lemma lemma_5_33_iii : ⟦ lim ∞ ⟧ (fun x => sqrt (x^2 + x) - x) = 1/2. Proof. Admitted.
Lemma lemma_5_33_iv : ¬ ∃ L, ⟦ lim ∞ ⟧ (fun x => x^2 * (1 + (sin x)^2) / (x + sin x)^2) = L. Proof. Admitted.
