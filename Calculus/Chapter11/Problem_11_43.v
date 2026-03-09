From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_43 : forall f,
  (forall x, x > 0 -> ⟦ der x ⟧ f = (fun _ => 1 / x)) ->
  f 1 = 0 ->
  forall x y, x > 0 -> y > 0 -> f (x * y) = f x + f y.
Admitted.
