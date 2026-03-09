From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_61_a : forall f f' a L1 L2,
  (exists δ, δ > 0 /\ forall x, 0 < |x - a| < δ -> ⟦ der x ⟧ f = f') ->
  ~ continuous_at f' a ->
  ⟦ lim a⁺ ⟧ f' = L1 ->
  ⟦ lim a⁻ ⟧ f' = L2 ->
  False.
Admitted.
