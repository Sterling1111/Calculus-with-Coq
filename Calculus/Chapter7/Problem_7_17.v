From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_17 : forall f,
  (exists l, f = polynomial l) ->
  exists y, forall x, | f y | <= | f x |.
Proof. Admitted.
