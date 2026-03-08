From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_17 : forall f (β : ℕ),
  0 < β < 1 -> (forall x, | f x | >= | x | ^ β) -> f 0 = 0 -> ~ differentiable_at f 0.
Proof.
Admitted.
