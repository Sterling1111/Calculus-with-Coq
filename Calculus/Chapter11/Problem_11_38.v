From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_38 : forall (n : nat) (a : nat -> R),
  ∑ 0 n (fun i => a i / INR (i + 1)) = 0 ->
  exists x, 0 < x < 1 /\ ∑ 0 n (fun i => a i * x^i) = 0.
Admitted.
