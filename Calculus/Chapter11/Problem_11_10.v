From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_10 : forall x y P,
  x > 0 -> y > 0 -> 2*x + 2*y = P ->
  x * y <= (P / 4)^2.
Admitted.
