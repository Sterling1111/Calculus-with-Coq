From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_4 : forall n S S',
  S = (fun x => x ^ n) -> ⟦ der ⟧ S = S' -> forall x, S' x = INR n * x ^ (n - 1).
Proof.
Admitted.
