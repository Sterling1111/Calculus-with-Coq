From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_8_a : forall f f' g g' c,
  g = (fun x => f (x + c)) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> forall x, g' x = f' (x + c).
Proof.
Admitted.

Lemma lemma_9_8_b : forall f f' g g' c,
  g = (fun x => f (c * x)) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> forall x, g' x = c * f' (c * x).
Proof.
Admitted.

Lemma lemma_9_8_c : forall f f' a,
  (forall x, f (x + a) = f x) -> differentiable f -> ⟦ der ⟧ f = f' -> (forall x, f' (x + a) = f' x).
Proof.
Admitted.
