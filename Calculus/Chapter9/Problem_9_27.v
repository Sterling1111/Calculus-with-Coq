From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_27 : forall n k S,
  (k <= n)%nat -> S = (fun y => y ^ n) -> 
  forall x, ⟦ Der ^ k x ⟧ S = INR (fact n) / INR (fact (n - k)) * x ^ (n - k).
Admitted.