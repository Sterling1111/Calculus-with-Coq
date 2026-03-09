From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_31_b : forall f a b x0,
  a < b ->
  integrable_on a b f ->
  (forall x, x ∈ [a, b] -> f x >= 0) ->
  continuous_at f x0 ->
  x0 ∈ [a, b] ->
  f x0 > 0 ->
  ∫ a b f > 0.
Admitted.

Lemma lemma_13_31_c : forall f a b,
  a < b ->
  integrable_on a b f ->
  (forall x, x ∈ [a, b] -> f x > 0) ->
  ∫ a b f > 0.
Admitted.
