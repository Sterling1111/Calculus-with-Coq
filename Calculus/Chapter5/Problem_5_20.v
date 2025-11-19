From Calculus.Chapter5 Require Import Prelude.
From Lib Require Import Rational.
Open Scope R_scope.

Lemma lemma_5_20 : ∀ (f : R → R) (a : R),
  (∀ x, rational x → f x = x) →
  (∀ x, irrational x → f x = - x) →
  a <> 0 →
  ∀ L, ~ (⟦ lim a ⟧ f = L).
Proof. Admitted.
