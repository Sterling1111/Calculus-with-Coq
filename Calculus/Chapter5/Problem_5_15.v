From Calculus.Chapter5 Require Import Prelude.

Section Problem_5_15.

Variable α : R.
Hypothesis H1 : ⟦ lim 0 ⟧ (fun x => sin x / x) = α.

Lemma lemma_5_15_i : ⟦ lim 0 ⟧ (fun x => sin (3 * x) / x) = 3 * α.
Proof. Admitted.

Lemma lemma_5_15_ii (a b : R) (H2 : b <> 0) : ⟦ lim 0 ⟧ (fun x => sin (a * x) / sin (b * x)) = a / b.
Proof. Admitted.

Lemma lemma_5_15_iii : ⟦ lim 0 ⟧ (fun x => (sin x)^2 / x) = 0.
Proof. Admitted.

Lemma lemma_5_15_iv : ⟦ lim 0 ⟧ (fun x => (sin (2 * x))^2 / x^2) = 4 * α^2.
Proof. Admitted.

Lemma lemma_5_15_v : ⟦ lim 0 ⟧ (fun x => (1 - cos x) / x^2) = α^2 / 2.
Proof. Admitted.

Lemma lemma_5_15_vi : ⟦ lim 0 ⟧ (fun x => ((tan x)^2 + 2 * x) / (x + x^2)) = 2.
Proof. Admitted.

Lemma lemma_5_15_vii : ⟦ lim 0 ⟧ (fun x => x * sin x / (1 - cos x)) = 2 / α.
Proof. Admitted.

Lemma lemma_5_15_viii (x : R) : ⟦ lim 0 ⟧ (fun h => (sin (x + h) - sin x) / h) = α * cos x.
Proof. Admitted.

Lemma lemma_5_15_ix : ⟦ lim 1 ⟧ (fun x => sin (x^2 - 1) / (x - 1)) = 2 * α.
Proof. Admitted.

Lemma lemma_5_15_x : ⟦ lim 0 ⟧ (fun x => x^2 * (3 + sin x) / (x + sin x)^2) = 3 / (1 + α)^2.
Proof. Admitted.

Lemma lemma_5_15_xi : ⟦ lim 1 ⟧ (fun x => (x^2 - 1)^3 * (sin (1 / (x - 1)))^3) = 0.
Proof. Admitted.

End Problem_5_15.