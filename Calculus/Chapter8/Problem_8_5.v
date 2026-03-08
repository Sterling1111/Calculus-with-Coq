From Calculus.Chapter8 Require Import Prelude.
From Lib Require Import Rational.

Lemma lemma_8_5_a : forall x y, y - x > 1 -> exists k : ℤ, x < IZR k < y.
Proof. Admitted.

Lemma lemma_8_5_b : forall x y : ℝ, x < y -> exists r : ℝ, rational r /\ x < r < y.
Proof. Admitted.

Lemma lemma_8_5_c : forall r s : ℝ, rational r -> rational s -> r < s -> exists t : ℝ, irrational t /\ r < t < s.
Proof. Admitted.

Lemma lemma_8_5_d : forall x y : ℝ, x < y -> exists t : ℝ, irrational t /\ x < t < y.
Proof. Admitted.
