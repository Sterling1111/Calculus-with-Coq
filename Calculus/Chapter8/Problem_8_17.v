From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_17_a_i : forall a x y,
  x ∈ (fun x => x < a) -> y < x -> y ∈ (fun x => x < a).
Proof. Admitted.

Lemma lemma_8_17_a_ii : forall a,
  (fun x => x < a) ≠ ∅.
Proof. Admitted.

Lemma lemma_8_17_a_iii : forall a,
  (fun x => x < a) ≠ (fun x => True).
Proof. Admitted.

Lemma lemma_8_17_a_iv : forall a x,
  x ∈ (fun x => x < a) -> exists x', x' ∈ (fun x => x < a) /\ x < x'.
Proof. Admitted.

Lemma lemma_8_17_b : forall A,
  (forall x y, x ∈ A -> y < x -> y ∈ A) ->
  A ≠ ∅ ->
  A ≠ (fun x => True) ->
  (forall x, x ∈ A -> exists x', x' ∈ A /\ x < x') ->
  has_upper_bound A ->
  forall supa, is_lub A supa ->
  (forall x, x ∈ A <-> x < supa).
Proof. Admitted.
