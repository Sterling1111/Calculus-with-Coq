From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_65 : forall (n : nat) x,
  (n >= 1)%nat ->
  x > -1 ->
  x <> 0 ->
  (1 + x)^n > 1 + INR n * x.
Admitted.
