From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_32_a : forall f a b,
  a < b ->
  continuous_on f [a, b] ->
  (forall g, continuous_on g [a, b] -> ∫ a b (f ⋅ g) = 0) ->
  forall x, x ∈ [a, b] -> f x = 0.
Admitted.

Lemma lemma_13_32_b : forall f a b,
  a < b ->
  continuous_on f [a, b] ->
  (forall g, continuous_on g [a, b] -> g a = 0 -> g b = 0 -> ∫ a b (f ⋅ g) = 0) ->
  forall x, x ∈ [a, b] -> f x = 0.
Admitted.
