From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_4_a : forall f g,
  increasing f ->
  increasing g ->
  increasing (fun x => f x + g x).
Admitted.

Lemma lemma_12_4_b : forall f g,
  increasing f ->
  increasing g ->
  increasing (f ∘ g)%function.
Admitted.
