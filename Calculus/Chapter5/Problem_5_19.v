From Calculus.Chapter5 Require Import Prelude.
From Lib Require Import Rational.
Open Scope R_scope.

Lemma lemma_5_19 : ∀ (f : R → R) (a : R),
  (∀ x, irrational x → f x = 0) →
  (∀ x, rational x → f x = 1) →
  ∀ L, ~ (⟦ lim a ⟧ f = L).
Proof. Admitted.
