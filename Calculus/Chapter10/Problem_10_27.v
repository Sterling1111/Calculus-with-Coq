From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_27_a : ∀ f a b g,
  a < b ->
  (∀ x, f x = (x - a) * (x - b) * g x) ->
  g a ≠ 0 -> g b ≠ 0 ->
  g a * g b > 0.
Proof. Admitted.

Lemma lemma_10_27_b : ∀ f a b g,
  a < b ->
  (∀ x, f x = (x - a) * (x - b) * g x) ->
  g a ≠ 0 -> g b ≠ 0 ->
  ∃ x, a < x < b /\ ⟦ Der x ⟧ f = 0.
Proof. Admitted.

Lemma lemma_10_27_c : ∀ f a b g (n m : nat),
  a < b ->
  (∀ x, f x = (x - a)^ INR m * (x - b)^ INR n * g x) ->
  g a ≠ 0 -> g b ≠ 0 ->
  ∃ x, a < x < b /\ ⟦ Der x ⟧ f = 0.
Proof. Admitted.
