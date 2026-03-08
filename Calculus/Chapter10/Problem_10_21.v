From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_21 : ∀ (n : nat) f g a,
  nth_differentiable_at n f (g a) ->
  nth_differentiable_at n g a ->
  nth_differentiable_at n (f ∘ g) a.
Proof.
Admitted.