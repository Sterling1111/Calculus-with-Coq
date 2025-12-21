From Calculus.Chapter1 Require Import Prelude.

Lemma lemma_1_20 : forall x x0 y y0 ε,
  |x - x0| < ε / 2 -> |y - y0| < ε / 2 -> (|(x + y) - (x0 + y0)| < ε /\ |(x - y) - (x0 - y0)| < ε).
Proof.
  solve_R.
Qed.
