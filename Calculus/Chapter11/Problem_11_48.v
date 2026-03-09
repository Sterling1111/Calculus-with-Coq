From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_48 : forall f f' a b L1 L2,
  a < b ->
  continuous_on f (a, b) ->
  ⟦ der ⟧ f (a, b) = f' ->
  ⟦ lim a⁺ ⟧ f = L1 ->
  ⟦ lim b⁻ ⟧ f = L2 ->
  exists x, x ∈ (a, b) /\ f' x = (L2 - L1) / (b - a).
Admitted.
