From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_13_a : forall f a b,
  a < b -> continuous_on f [a, b] -> exists g,
    (forall x, x ∈ [a, b] -> g x = f x) /\ continuous_on g ℝ.
Proof.
  intros f a b H1 H2. admit.
Admitted.