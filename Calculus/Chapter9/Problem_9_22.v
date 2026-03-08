From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_22_a : forall f f' x,
  ⟦ der x ⟧ f = f' ->
  ⟦ lim 0 ⟧ (fun h => (f (x + h) - f (x - h)) / (2 * h)) = f' x.
Proof.
Admitted.

Lemma lemma_9_22_b : forall f f' x,
  ⟦ der x ⟧ f = f' ->
  True. (* limit over two variables h, k approaches 0+ *)
Proof.
Admitted.
