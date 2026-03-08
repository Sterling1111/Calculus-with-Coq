From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_8 : ∀ r1 r2 A1 A2 t,
  (∀ t, A1 t = π * (r1 t)^2) ->
  (∀ t, A2 t = π * (r2 t)^2) ->
  (∀ t, A1 t - A2 t = 9 * π) ->
  ⟦ Der t ⟧ A1 = 10 * π ->
  A2 t = 16 * π ->
  ⟦ Der t ⟧ (λ t, 2 * π * r2 t) = 5 * π / 4.
Proof. Admitted.
