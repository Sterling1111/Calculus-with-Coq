From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_16 : forall f a b c,
  a < b -> c > 0 ->
  integrable_on (c * a) (c * b) f ->
  ∫ (c * a) (c * b) f = c * ∫ a b (fun t => f (c * t)).
Admitted.
