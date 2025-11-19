From Calculus.Chapter5 Require Import Prelude.

Definition wrong_def_5_26_a (f : R → R) (a l : R) : Prop :=
  ∀ δ, δ > 0 → ∃ ε, ε > 0 /\ ∀ x, 0 < |x - a| < δ → |f x - l| < ε.

Lemma lemma_5_26_a : ∃ (f : R → R) (a l : R),
  wrong_def_5_26_a f a l /\ ¬ (⟦ lim a ⟧ f = l).
Proof. Admitted.

Definition wrong_def_5_26_b (f : R → R) (a l : R) : Prop :=
  ∀ ε, ε > 0 → ∃ δ, δ > 0 /\ ∀ x, |f x - l| < ε → 0 < |x - a| < δ.

Lemma lemma_5_26_b : ∃ (f : R → R) (a l : R),
  wrong_def_5_26_b f a l /\ ¬ (⟦ lim a ⟧ f = l).
Proof. Admitted.
