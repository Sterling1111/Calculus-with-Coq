From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_23_a : forall f a b m M,
  a < b ->
  integrable_on a b f ->
  (forall x, x ∈ [a, b] -> m <= f x <= M) ->
  exists mu, m <= mu <= M /\ ∫ a b f = (b - a) * mu.
Admitted.

Lemma lemma_13_23_b : forall f a b,
  a < b ->
  continuous_on f [a, b] ->
  exists xi, xi ∈ [a, b] /\ ∫ a b f = (b - a) * f xi.
Admitted.

Lemma lemma_13_23_d : forall f g a b,
  a < b ->
  continuous_on f [a, b] ->
  integrable_on a b g ->
  (forall x, x ∈ [a, b] -> g x >= 0) ->
  exists xi, xi ∈ [a, b] /\ ∫ a b (f ⋅ g) = f xi * ∫ a b g.
Admitted.

Lemma lemma_13_23_e : forall f g a b,
  a < b ->
  continuous_on f [a, b] ->
  integrable_on a b g ->
  (forall x, x ∈ [a, b] -> g x <= 0) ->
  exists xi, xi ∈ [a, b] /\ ∫ a b (f ⋅ g) = f xi * ∫ a b g.
Admitted.
