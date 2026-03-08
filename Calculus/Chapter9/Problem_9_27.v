From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_27 : forall n k S,
  (k <= n)%nat -> S = (fun x => x ^ n) -> 
  forall x, ⟦ Der ^ k ⟧ S x = INR (fact n) / INR (fact (n - k)) * x ^ (n - k).
Proof.
Admitted.
