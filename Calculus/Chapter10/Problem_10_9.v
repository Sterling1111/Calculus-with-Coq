From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_9 : ∀ a b d t,
  (∀ t, a t > 0) -> 
  (∀ t, b t <= 0) -> 
  (∀ t, d t = √ ((a t)^2 + (- √ 3 * b t)^2)) ->
  a t = 5 -> ⟦ Der t ⟧ a = 3 ->
  √ ((- √ 3 * b t)^2 + (b t)^2) = 3 ->
  ⟦ Der t ⟧ (λ t, √ ((- √ 3 * b t)^2 + (b t)^2)) = 4 ->
  True.
Proof. Admitted.
