From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_38_d : forall f g a b,
  a < b ->
  integrable_on a b f ->
  integrable_on a b g ->
  (forall x, x ∈ [a, b] -> f x >= 0) ->
  (forall x, x ∈ [a, b] -> g x >= 0) ->
  integrable_on a b (f ⋅ g).
Admitted.

Lemma lemma_13_38_e : forall f g a b,
  a < b ->
  integrable_on a b f ->
  integrable_on a b g ->
  integrable_on a b (f ⋅ g).
Admitted.
