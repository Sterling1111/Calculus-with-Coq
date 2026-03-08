From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_11_a : forall a : sequence,
  (forall n, a n > 0) -> 
  (forall n, a (S n) <= a n / 2) ->
  forall ε : ℝ, ε > 0 -> exists n : ℕ, a n < ε.
Proof. Admitted.
