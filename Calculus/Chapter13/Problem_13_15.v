From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_15 : forall a b,
  a > 1 -> b > 1 ->
  ∫ 1 a (fun t => 1 / t) + ∫ 1 b (fun t => 1 / t) = ∫ 1 (a * b) (fun t => 1 / t).
Admitted.
