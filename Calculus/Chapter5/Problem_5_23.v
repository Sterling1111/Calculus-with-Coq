From Calculus.Chapter5 Require Import Prelude.

Definition no_limit_at (a : R) (f : R → R) : Prop :=
  ∀ L, ¬ (⟦ lim a ⟧ f = L).

Definition lim_abs_to_infty_at (a : R) (f : R → R) : Prop :=
  ∀ M, M > 0 → ∃ δ, δ > 0 /\ ∀ x, 0 < |x - a| < δ → |f x| > M.

Lemma lemma_5_23_a : ∀ (f g : R → R) (a L : R),
  ⟦ lim a ⟧ f = L → L ≠ 0 →
  no_limit_at a g →
  no_limit_at a (fun x => f x * g x).
Proof. Admitted.

Lemma lemma_5_23_b : ∀ (f g : R → R) (a : R),
  lim_abs_to_infty_at a f →
  no_limit_at a g →
  no_limit_at a (fun x => f x * g x).
Proof. Admitted.

Lemma lemma_5_23_c : ∀ (f : R → R) (a : R),
  (¬ (∃ L, ⟦ lim a ⟧ f = L /\ L ≠ 0)) →
  (¬ lim_abs_to_infty_at a f) →
  ∃ g, no_limit_at a g /\ ∃ L, ⟦ lim a ⟧ (fun x => f x * g x) = L.
Proof. Admitted.
