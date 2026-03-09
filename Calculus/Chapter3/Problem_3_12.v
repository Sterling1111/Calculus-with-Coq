From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_12_d : forall f : R -> R, 
  even_f f -> exists g : R -> R, forall x, f x = g (| x |).
Proof.
Admitted.
