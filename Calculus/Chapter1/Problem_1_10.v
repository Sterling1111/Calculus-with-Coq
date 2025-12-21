From Calculus.Chapter1 Require Import Prelude.

Lemma lemma_1_10_i : forall a b,
  ((a >= -b /\ b >= 0) -> |a + b| - |b| = a) /\
  ((a <= -b /\ b <= 0) -> |a + b| - |b| = -a) /\
  ((a >= -b /\ b <= 0) -> |a + b| - |b| = a + 2 * b) /\
  ((a <= -b /\ b >= 0) -> |a + b| - |b| = -a - 2 * b).
Proof.
  solve_R.
Qed.

Lemma lemma_1_10_ii : forall x,
  (x >= 1 <-> |(|x| - 1)| = x - 1) /\
  (0 <= x <= 1 <-> |(|x| - 1)| = 1 - x) /\
  (-1 <= x <= 0 <-> |(|x| - 1)| = 1 + x) /\
  (x <= -1 <-> |(|x| - 1)| = -1 - x).
Proof.
  solve_R.
Qed.

Lemma lemma_1_10_iii : forall x,
  (x >= 0 <-> |x| - |x^2| = x - x^2) /\
  (x <= 0 <-> |x| - |x^2| = -x - x^2).
Proof.
  solve_R.
Qed.

Lemma lemma_1_10_iv : forall a,
  (a >= 0 <-> a - |(a - |a|)| = a) /\
  (a <= 0 <-> a - |(a - |a|)| = 3 * a).
Proof.
  solve_R.
Qed.