From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_6_a : forall f f' g g' c,
  g = (fun x => f x + c) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> forall x, g' x = f' x.
Proof.
Admitted.

Lemma lemma_9_6_b : forall f f' g g' c,
  g = (fun x => c * f x) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> forall x, g' x = c * f' x.
Proof.
Admitted.
