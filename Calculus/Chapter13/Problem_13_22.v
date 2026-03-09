From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_22 : forall f f_inv a b,
  f 0 = 0 ->
  continuous_on f [0, Rmax a (f_inv b)] ->
  increasing_on f [0, Rmax a (f_inv b)] ->
  inverse f f_inv ->
  a > 0 -> b > 0 ->
  a * b <= ∫ 0 a f + ∫ 0 b f_inv /\ (a * b = ∫ 0 a f + ∫ 0 b f_inv <-> b = f a).
Admitted.
