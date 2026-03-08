From Calculus.Chapter8 Require Import Prelude.

Definition shadow_point (f : R -> R) (x : R) :=
  exists y, y > x /\ f y > f x.

Lemma lemma_8_20_a : forall f a b,
  continuous f ->
  (forall x, a < x < b -> shadow_point f x) ->
  ~ shadow_point f a ->
  ~ shadow_point f b ->
  f a > f b ->
  forall x, a <= x <= b -> f x <= f a.
Proof. Admitted.

Lemma lemma_8_20_b : forall f a b,
  continuous f ->
  a < b ->
  (forall x, a < x < b -> shadow_point f x) ->
  ~ shadow_point f a ->
  ~ shadow_point f b ->
  f a = f b.
Proof. Admitted.
