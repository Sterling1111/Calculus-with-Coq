From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_19_a : forall f f' g h h' a,
  f a = g a /\ g a = h a ->
  (forall x, f x <= g x /\ g x <= h x) ->
  ⟦ der a ⟧ f = f' -> ⟦ der a ⟧ h = h' ->
  f' a = h' a ->
  exists g', ⟦ der a ⟧ g = g' /\ g' a = f' a.
Proof.
Admitted.

Lemma lemma_9_19_b : ~ (forall f f' g h h' a,
  (forall x, f x <= g x /\ g x <= h x) ->
  ⟦ der a ⟧ f = f' -> ⟦ der a ⟧ h = h' ->
  f' a = h' a ->
  exists g', ⟦ der a ⟧ g = g' /\ g' a = f' a).
Proof.
Admitted.
