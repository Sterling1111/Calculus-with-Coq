From Calculus.Chapter8 Require Import Prelude.

Definition dense (A : Ensemble ℝ) :=
  forall x y : ℝ, x < y -> exists z, z ∈ A /\ x < z < y.

Lemma lemma_8_6_a : forall f A,
  continuous f -> dense A -> (forall x, x ∈ A -> f x = 0) -> forall x, f x = 0.
Proof. Admitted.

Lemma lemma_8_6_b : forall f g A,
  continuous f -> continuous g -> dense A -> (forall x, x ∈ A -> f x = g x) -> forall x, f x = g x.
Proof. Admitted.

Lemma lemma_8_6_c : forall f g A,
  continuous f -> continuous g -> dense A -> (forall x, x ∈ A -> f x >= g x) -> forall x, f x >= g x.
Proof. Admitted.
