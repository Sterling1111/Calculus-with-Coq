From Calculus.Chapter7 Require Import Prelude.

Definition exactly_twice (f : R -> R) (y : R) :=
  exists x1 x2, x1 <> x2 /\ f x1 = y /\ f x2 = y /\
  forall x, f x = y -> x = x1 \/ x = x2.

Definition takes_0_or_2 (f : R -> R) (y : R) :=
  (forall x, f x <> y) \/ exactly_twice f y.

Lemma lemma_7_21_a : ~ (exists f,
  continuous f /\ forall y, exactly_twice f y).
Proof. Admitted.

Lemma lemma_7_21_b : ~ (exists f,
  continuous f /\ forall y, takes_0_or_2 f y).
Proof. Admitted.
