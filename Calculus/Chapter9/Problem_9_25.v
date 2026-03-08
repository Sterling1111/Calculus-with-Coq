From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_25_even : forall f k,
  even_f f -> 
  even_f (⟦ Der ^ (2 * k) ⟧ f) /\ odd_f (⟦ Der ^ (2 * k + 1) ⟧ f).
Proof.
Admitted.

Lemma lemma_9_25_odd : forall f k,
  odd_f f -> 
  odd_f (⟦ Der ^ (2 * k) ⟧ f) /\ even_f (⟦ Der ^ (2 * k + 1) ⟧ f).
Proof.
Admitted.
