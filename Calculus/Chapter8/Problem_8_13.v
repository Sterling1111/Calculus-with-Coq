From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_13 : forall A B supa supb supab,
  A ≠ ∅ -> B ≠ ∅ -> has_upper_bound A -> has_upper_bound B ->
  is_lub A supa -> is_lub B supb -> 
  is_lub (fun z => exists x y, x ∈ A /\ y ∈ B /\ z = x + y) supab ->
  supab = supa + supb.
Proof. Admitted.
