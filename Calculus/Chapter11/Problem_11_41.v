From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_41_a : 
  exists x1 x2, x1 <> x2 /\ 
  (fun x => x^2 - cos x) x1 = 0 /\ 
  (fun x => x^2 - cos x) x2 = 0 /\ 
  (forall x, (fun y => y^2 - cos y) x = 0 -> x = x1 \/ x = x2).
Admitted.
