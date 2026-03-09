From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_27_a : forall f,
  (forall x, f x > 0) ->
  decreasing f ->
  exists g, continuous g /\ decreasing g /\ forall x, 0 < g x <= f x.
Admitted.

Lemma lemma_12_27_b : forall f,
  (forall x, f x > 0) ->
  decreasing f ->
  exists g, continuous g /\ decreasing g /\ (forall x, 0 < g x <= f x) /\ ⟦ lim ∞ ⟧ (fun x => g x / f x) = 0.
Admitted.
