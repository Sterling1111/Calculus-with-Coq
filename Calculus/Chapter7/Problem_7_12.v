From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_12_a : forall f,
  continuous_on f [0, 1] ->
  (forall x, x ∈ [0, 1] -> f x ∈ [0, 1]) ->
  exists x, x ∈ [0, 1] /\ f x = 1 - x.
Proof. Admitted.

Lemma lemma_7_12_b : forall f g,
  continuous_on f [0, 1] ->
  (forall x, x ∈ [0, 1] -> f x ∈ [0, 1]) ->
  continuous_on g [0, 1] ->
  ((g 0 = 0 /\ g 1 = 1) \/ (g 0 = 1 /\ g 1 = 0)) ->
  exists x, x ∈ [0, 1] /\ f x = g x.
Proof. Admitted.
