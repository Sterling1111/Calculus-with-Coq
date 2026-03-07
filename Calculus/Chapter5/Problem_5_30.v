From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_30_i : ∀ (f : R -> R) L,
  ⟦ lim 0⁺ ⟧ f = L <-> ⟦ lim 0⁻ ⟧ (fun x => f (-x)) = L.
Proof. Admitted.

Lemma lemma_5_30_ii : ∀ (f : R -> R) L,
  ⟦ lim 0 ⟧ (fun x => f (|x|)) = L <-> ⟦ lim 0⁺ ⟧ f = L.
Proof. Admitted.

Lemma lemma_5_30_iii : ∀ (f : R -> R) L,
  ⟦ lim 0 ⟧ (fun x => f (x^2)) = L <-> ⟦ lim 0⁺ ⟧ f = L.
Proof. Admitted.
