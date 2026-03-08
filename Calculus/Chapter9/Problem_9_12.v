From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_12_a : forall a a' L,
  ⟦ der ⟧ a = a' -> (forall t, a' t = L (a t)).
Proof.
Admitted.

Lemma lemma_9_12_b : forall a a' b b' L,
  ⟦ der ⟧ a = a' -> ⟦ der ⟧ b = b' ->
  (forall t, a' t = L (a t)) ->
  (forall t, b t = a (t - 1)) ->
  (forall t, b' t = L (b t)).
Proof.
Admitted.

Lemma lemma_9_12_c : forall a a' b b' L c,
  ⟦ der ⟧ a = a' -> ⟦ der ⟧ b = b' ->
  (forall t, a' t = L (a t)) ->
  (forall t, b t = a t - c) ->
  (forall t, b' t = L (b t)) -> 
  (forall t, L (a t) = L (a t - c)).
Proof.
Admitted.
