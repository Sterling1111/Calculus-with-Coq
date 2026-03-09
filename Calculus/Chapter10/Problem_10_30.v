From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_30 : forall (n k : nat) x,
  (n > 0)%nat -> 
  x <> 0 ->
  ⟦ Der ^ k x ⟧ (fun t => 1 / t ^ n) = (-1)^k * (INR (fact (n + k - 1)) / INR (fact (n - 1))) * (1 / x ^ (n + k)) /\
  ⟦ Der ^ k x ⟧ (fun t => 1 / t ^ n) = (-1)^k * INR (fact k) * ((n + k - 1) ∁ k) * (1 / x ^ (n + k)).
Proof.
Admitted.