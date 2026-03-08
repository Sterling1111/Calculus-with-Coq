From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_13_b : forall f,
  (forall a b c, a < b ->
   (f a < c < f b \/ f b < c < f a) -> exists x, x ∈ [a, b] /\ f x = c) ->
  (forall y, exists! x, f x = y) ->
  continuous f.
Proof. Admitted.
