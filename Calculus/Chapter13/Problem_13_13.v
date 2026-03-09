From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_13_a : forall f a b,
  a <= b ->
  integrable_on a b f ->
  (forall x, x ∈ [a, b] -> f x >= 0) ->
  ∫ a b f >= 0.
Admitted.

Lemma lemma_13_13_b : forall f g a b,
  a <= b ->
  integrable_on a b f ->
  integrable_on a b g ->
  (forall x, x ∈ [a, b] -> f x >= g x) ->
  ∫ a b f >= ∫ a b g.
Admitted.
