From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_16 : forall f (α : ℕ),
  α > 1 -> (forall x, | f x | <= | x | ^ α) -> differentiable_at f 0.
Proof.
Admitted.
