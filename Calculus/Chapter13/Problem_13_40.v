From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_40 : forall f L,
  (forall x, x > 0 -> integrable_on 0 x f) ->
  ⟦ lim ∞ ⟧ f = L ->
  ⟦ lim ∞ ⟧ (fun x => (1 / x) * ∫ 0 x f) = L.
Admitted.
