From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_10_a : forall a x,
  a > 0 -> exists k : ℤ, exists x', x = IZR k * a + x' /\ 0 <= x' < a.
Proof. Admitted.

Lemma lemma_8_10_b : forall a x k1 k2 x1 x2,
  a > 0 -> x = IZR k1 * a + x1 -> 0 <= x1 < a ->
  x = IZR k2 * a + x2 -> 0 <= x2 < a ->
  k1 = k2 /\ x1 = x2.
Proof. Admitted.
