From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_14_a : ∀ (f : R -> R) (l b : R),
  ⟦ lim 0 ⟧ (fun x => f x / x) = l -> b <> 0 ->
  ⟦ lim 0 ⟧ (fun x => f (b * x) / x) = b * l.
Proof. Admitted.

Lemma lemma_5_14_b : ∀ (f : R -> R) (l : R),
  f 0 = 0 ->
  ⟦ lim 0 ⟧ (fun x => f x / x) = l ->
  ⟦ lim 0 ⟧ (fun x => f (0 * x) / x) = 0.
Proof. Admitted.
