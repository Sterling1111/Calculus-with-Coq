From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_8_a_1 : ∃ (f g : R -> R) (a L : R),
  (∀ Lf, ¬ (⟦ lim a ⟧ f = Lf)) /\ (∀ Lg, ¬ (⟦ lim a ⟧ g = Lg)) /\
  ⟦ lim a ⟧ (fun x => f x + g x) = L.
Proof. Admitted.

Lemma lemma_5_8_a_2 : ∃ (f g : R -> R) (a L : R),
  (∀ Lf, ¬ (⟦ lim a ⟧ f = Lf)) /\ (∀ Lg, ¬ (⟦ lim a ⟧ g = Lg)) /\
  ⟦ lim a ⟧ (fun x => f x * g x) = L.
Proof. Admitted.

Lemma lemma_5_8_b : ∀ (f g : R -> R) (a L L_sum : R),
  ⟦ lim a ⟧ f = L -> ⟦ lim a ⟧ (fun x => f x + g x) = L_sum ->
  ∃ Lg, ⟦ lim a ⟧ g = Lg.
Proof. Admitted.

Lemma lemma_5_8_c : ∀ (f g : R -> R) (a L : R),
  ⟦ lim a ⟧ f = L -> (∀ Lg, ¬ (⟦ lim a ⟧ g = Lg)) ->
  ∀ L_sum, ¬ (⟦ lim a ⟧ (fun x => f x + g x) = L_sum).
Proof. Admitted.

Lemma lemma_5_8_d : ∃ (f g : R -> R) (a L L_prod : R),
  ⟦ lim a ⟧ f = L /\ ⟦ lim a ⟧ (fun x => f x * g x) = L_prod /\
  (∀ Lg, ¬ (⟦ lim a ⟧ g = Lg)).
Proof. Admitted.
