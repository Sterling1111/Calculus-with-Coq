From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_7 : forall f,
  continuous f -> (forall x y, f (x + y) = f x + f y) -> exists c, forall x, f x = c * x.
Proof. Admitted.
