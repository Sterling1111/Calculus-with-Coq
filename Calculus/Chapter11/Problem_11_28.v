From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_28_a : forall f f' a b M,
  a < b ->
  continuous_on f [a, b] ->
  ⟦ der ⟧ f (a, b) = f' ->
  (forall x, x ∈ (a, b) -> f' x >= M) ->
  f b >= f a + M * (b - a).
Admitted.

Lemma lemma_11_28_b : forall f f' a b M,
  a < b ->
  continuous_on f [a, b] ->
  ⟦ der ⟧ f (a, b) = f' ->
  (forall x, x ∈ (a, b) -> f' x <= M) ->
  f b <= f a + M * (b - a).
Admitted.

Lemma lemma_11_28_c : forall f f' a b M,
  a < b ->
  continuous_on f [a, b] ->
  ⟦ der ⟧ f (a, b) = f' ->
  (forall x, x ∈ (a, b) -> |f' x| <= M) ->
  |f b - f a| <= M * (b - a).
Admitted.
