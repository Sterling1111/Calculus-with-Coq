From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_20_a : forall f f' a d,
  f = (fun x => x^4) ->
  ⟦ der a ⟧ f = f' ->
  d = (fun x => f x - f' a * (x - a) - f a) ->
  exists q, forall x, d x = (x - a)^2 * q x.
Proof.
Admitted.

Lemma lemma_9_20_b : forall f f' a d,
  f = (fun x => x^4) ->
  ⟦ der a ⟧ f = f' ->
  d = (fun x => f x - f' a * (x - a) - f a) ->
  (forall x, x <> a -> d x / (x - a) = (f x - f a) / (x - a) - f' a) /\
  (exists h, (forall x, x <> a -> h x = d x / (x - a)) /\ ⟦ lim a ⟧ h = 0 /\ h a = 0).
Proof.
Admitted.
