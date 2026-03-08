From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_5 : forall a,
  exists f, continuous_at f a /\ (forall x, x <> a -> ~ continuous_at f x).
Proof. Admitted.
