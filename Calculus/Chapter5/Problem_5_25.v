From Calculus.Chapter5 Require Import Prelude.
Open Scope R_scope.

Definition def_5_25_i (f : R → R) (a l : R) : Prop :=
  ∀ δ, δ > 0 → ∃ ε, ε > 0 /\ ∀ x, 0 < |x - a| < ε → |f x - l| < δ.

Definition def_5_25_ii (f : R → R) (a l : R) : Prop :=
  ∀ δ, δ > 0 → ∃ ε, ε > 0 /\ ∀ x, 0 < |x - a| < ε → |f x - l| <= δ.

Definition def_5_25_iii (f : R → R) (a l : R) : Prop :=
  ∀ δ, δ > 0 → ∃ ε, ε > 0 /\ ∀ x, 0 < |x - a| < ε → |f x - l| <= 5 * δ.

Definition def_5_25_iv (f : R → R) (a l : R) : Prop :=
  ∀ δ, δ > 0 → ∃ ε, ε > 0 /\ ∀ x, 0 < |x - a| < ε / 10 → |f x - l| < δ.

Lemma lemma_5_25_i : ∀ f a l, ⟦ lim a ⟧ f = l <-> def_5_25_i f a l.
Proof. Admitted.

Lemma lemma_5_25_ii : ∀ f a l, ⟦ lim a ⟧ f = l <-> def_5_25_ii f a l.
Proof. Admitted.

Lemma lemma_5_25_iii : ∀ f a l, ⟦ lim a ⟧ f = l <-> def_5_25_iii f a l.
Proof. Admitted.

Lemma lemma_5_25_iv : ∀ f a l, ⟦ lim a ⟧ f = l <-> def_5_25_iv f a l.
Proof. Admitted.
