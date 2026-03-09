From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_13_a : forall f : R -> R, 
  exists E O : R -> R, even_f E /\ odd_f O /\ forall x, f x = E x + O x.
Proof.
Admitted.

Lemma lemma_3_13_b : forall f E1 O1 E2 O2 : R -> R, 
  even_f E1 -> odd_f O1 -> (forall x, f x = E1 x + O1 x) -> 
  even_f E2 -> odd_f O2 -> (forall x, f x = E2 x + O2 x) -> 
  (forall x, E1 x = E2 x) /\ (forall x, O1 x = O2 x).
Proof.
Admitted.
