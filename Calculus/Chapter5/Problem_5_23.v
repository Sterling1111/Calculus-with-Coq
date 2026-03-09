From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_23_a : ∀ (f g : R → R) (a L : R),
  ⟦ lim a ⟧ f = L → L ≠ 0 →
  (~ ∃ L1, ⟦ lim a ⟧ g = L1) →
  (~ ∃ L2, ⟦ lim a ⟧ (fun x => f x * g x) = L2).
Proof. Admitted.

Lemma lemma_5_23_b : ∀ (f g : R → R) (a : R),
  ⟦ lim a ⟧ (fun x => |f x|) = ∞ ->
  (~ ∃ L1, ⟦ lim a ⟧ g = L1) ->
  (~ ∃ L2, ⟦ lim a ⟧ (fun x => f x * g x) = L2).
Proof. Admitted.

Lemma lemma_5_23_c : ∀ (f : R → R) (a : R),
  (~ ∃ L, ⟦ lim a ⟧ f = L /\ L ≠ 0) ->
  (~ (⟦ lim a ⟧ (fun x => |f x|) = ∞ )) ->
  ∃ g, (~ ∃ L1, ⟦ lim a ⟧ g = L1) /\ ∃ L2, ⟦ lim a ⟧ (fun x => f x * g x) = L2.
Proof. Admitted.