From Calculus.Chapter10 Require Import Prelude.

Definition double_root (f : ℝ -> ℝ) (a : ℝ) : Prop :=
  ∃ g, (∀ x, f x = (x - a)^2 * g x).

Lemma lemma_10_24_a : ∀ f a,
  (∃ g, ∀ x, f x = (x - a) * g x) ->
  (double_root f a <-> f a = 0 /\ ⟦ Der a ⟧ f = 0).
Proof. Admitted.

Lemma lemma_10_24_b : ∀ a b c,
  a ≠ 0 ->
  (double_root (λ x, a * x^2 + b * x + c) (- b / (2 * a)) <-> b^2 - 4 * a * c = 0).
Proof. Admitted.
