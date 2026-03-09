From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_19 : forall f a b x0,
  a < b ->
  bounded_on f [a, b] ->
  x0 ∈ (a, b) ->
  (forall x, x ∈ [a, b] -> x <> x0 -> continuous_at f x) ->
  integrable_on a b f.
Admitted.
