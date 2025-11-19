From Calculus.Chapter5 Require Import Prelude.
From Lib Require Import Sets Notations.
Import SetNotations IntervalNotations.
Open Scope R_scope.

Section Problem_5_24.
  Variable A : nat → Ensemble R.
  Variable f : R → R.

  Hypothesis A_finite : ∀ n, Finite_set (A n).
  Hypothesis A_in_unit : ∀ n, (A n) ⊆ [0,1].
  Hypothesis A_disjoint : ∀ m n, m <> n → (A m) ⋂ (A n) = ∅.

  Hypothesis f_spec_in : ∀ x n, x ∈ A n → f x = / INR n.
  Hypothesis f_spec_out : ∀ x, (∀ n, x ∉ A n) → f x = 0.

  Lemma lemma_5_24 : ∀ a, a ∈ [0,1] → ⟦ lim a ⟧ f = 0.
  Proof. Admitted.
End Problem_5_24.
