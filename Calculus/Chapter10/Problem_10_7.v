From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_7_a : ∀ r A, (∀ t, A t = π * (r t)^2) ->
  (∀ t, r t = 6 -> ⟦ Der t ⟧ r = 4) -> (∀ t, r t = 6 -> ⟦ Der t ⟧ A = 48 * π).
Proof. Admitted.

Lemma lemma_10_7_b : ∀ r V, (∀ t, V t = 4 / 3 * π * (r t)^3) ->
  (∀ t, r t = 6 -> ⟦ Der t ⟧ V = 2) -> (∀ t, r t = 6 -> ⟦ Der t ⟧ r = 1 / (72 * π)).
Proof. Admitted.

Lemma lemma_10_7_c : ∀ r A V, (∀ t, A t = π * (r t)^2) ->
  (∀ t, V t = 4 / 3 * π * (r t)^3) ->
  (∀ t, r t = 3 -> ⟦ Der t ⟧ A = 5) -> (∀ t, r t = 3 -> ⟦ Der t ⟧ V = 10).
Proof. Admitted.
