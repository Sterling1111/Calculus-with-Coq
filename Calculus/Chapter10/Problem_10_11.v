From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_11 : ∀ f g,
  (∀ x, x ≠ 0 -> f x = g x * sin (1 / x)) ->
  f 0 = 0 ->
  g 0 = 0 ->
  ⟦ Der 0 ⟧ g = 0 ->
  ⟦ Der 0 ⟧ f = 0.
Proof. Admitted.
