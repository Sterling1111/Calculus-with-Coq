From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_3_b : forall (p : nat) b,
  b > 0 ->
  ∫ 0 b (fun x => x^p) = b^(p+1) / INR (p+1).
Admitted.
