From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_60_a : forall f f' a b,
  a < b ->
  ⟦ der ⟧ f [a, b] = f' ->
  minimum_point f [a, b] a ->
  f' a >= 0.
Admitted.

Lemma lemma_11_60_b : forall f f' a b,
  a < b ->
  ⟦ der ⟧ f [a, b] = f' ->
  f' a < 0 -> f' b > 0 ->
  exists x, x ∈ (a, b) /\ f' x = 0.
Admitted.

Lemma lemma_11_60_c : forall f f' a b c,
  a < b ->
  ⟦ der ⟧ f [a, b] = f' ->
  (f' a < c /\ c < f' b) \/ (f' b < c /\ c < f' a) ->
  exists x, x ∈ (a, b) /\ f' x = c.
Admitted.
