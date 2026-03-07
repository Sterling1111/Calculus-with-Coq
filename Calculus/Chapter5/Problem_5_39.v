From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_39_i : ⟦ lim ∞ ⟧ (fun x => (x^3 + 4*x - 7) / (7*x^2 - x + 1)) = ∞. Proof. Admitted.
Lemma lemma_5_39_ii : ⟦ lim ∞ ⟧ (fun x => x * (1 + (sin x)^2)) = ∞. Proof. Admitted.
Lemma lemma_5_39_iii : ¬ ∃ L, ⟦ lim ∞ ⟧ (fun x => x * (sin x)^2) = L. Proof. Admitted.
Lemma lemma_5_39_iv : ⟦ lim ∞ ⟧ (fun x => x^2 * sin (1 / x)) = ∞. Proof. Admitted.
Lemma lemma_5_39_v : ⟦ lim ∞ ⟧ (fun x => sqrt (x^2 + 2*x) - x) = 1. Proof. Admitted.
Lemma lemma_5_39_vi : ⟦ lim ∞ ⟧ (fun x => x * (sqrt (x + 2) - sqrt x)) = ∞. Proof. Admitted.
Lemma lemma_5_39_vii : ⟦ lim ∞ ⟧ (fun x => sqrt (Rabs x) / x) = 0. Proof. Admitted.
