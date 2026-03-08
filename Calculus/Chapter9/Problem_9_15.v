From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_15_a : forall f,
  (forall x, | f x | <= x^2) -> differentiable_at f 0.
Proof.
Admitted.

Lemma lemma_9_15_b : forall f g,
  differentiable_at g 0 -> g 0 = 0 -> ⟦ der 0 ⟧ g = (fun _ => 0) ->
  (forall x, | f x | <= | g x |) -> differentiable_at f 0.
Proof.
Admitted.
