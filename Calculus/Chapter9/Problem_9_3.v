From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_3 : forall a f f',
  a > 0 -> f = (fun x => sqrt x) -> ⟦ der a ⟧ f = f' -> f' a = 1 / (2 * sqrt a).
Proof.
Admitted.
