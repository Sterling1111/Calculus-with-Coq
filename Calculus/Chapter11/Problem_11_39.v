From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_39 : forall m,
  ~ (exists x y, 0 <= x /\ x < y /\ y <= 1 /\
     x^3 - 3*x + m = 0 /\ y^3 - 3*y + m = 0).
Admitted.
