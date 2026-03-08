From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_12_a : forall A B supa,
  A ≠ ∅ -> B ≠ ∅ -> (forall x y, x ∈ A -> y ∈ B -> x <= y) ->
  is_lub A supa -> forall y, y ∈ B -> supa <= y.
Proof. Admitted.

Lemma lemma_8_12_b : forall A B supa infb,
  A ≠ ∅ -> B ≠ ∅ -> (forall x y, x ∈ A -> y ∈ B -> x <= y) ->
  is_lub A supa -> is_glb B infb -> supa <= infb.
Proof. Admitted.
