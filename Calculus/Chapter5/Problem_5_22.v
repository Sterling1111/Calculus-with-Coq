From Calculus.Chapter5 Require Import Prelude.
Open Scope R_scope.

Definition no_limit_at (a : R) (f : R → R) : Prop :=
  ∀ L, ~ (⟦ lim a ⟧ f = L).

Definition preserves_nonexistence_by_sum_at_0 (f : R → R) : Prop :=
  ∀ g, no_limit_at 0 g → no_limit_at 0 (fun x => f x + g x).

Lemma lemma_5_22_if : ∀ (f : R → R) (L : R),
  ⟦ lim 0 ⟧ f = L → preserves_nonexistence_by_sum_at_0 f.
Proof. Admitted.

Lemma lemma_5_22_only_if : ∀ (f : R → R),
  preserves_nonexistence_by_sum_at_0 f → ∃ L, ⟦ lim 0 ⟧ f = L.
Proof. Admitted.
