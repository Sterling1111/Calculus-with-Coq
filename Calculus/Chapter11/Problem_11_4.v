From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_4_a : forall (n : nat) (a : nat -> R),
  (n > 0)%nat ->
  minimum_point (fun x => ∑ 1 n (fun i => (x - a i)^2)) ℝ ( (∑ 1 n a) / INR n ).
Admitted.
