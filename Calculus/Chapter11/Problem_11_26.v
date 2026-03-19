From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_26 : ∀ l n,
  degree l = n ->
  let f := λ x, polynomial l x in
  (∀ x, f x >= 0) ->
  ∀ x, ∑ 0 n (λ i, ⟦ Der^i x ⟧ f) >= 0.
Proof.
  intros l n H1 f H2 x.
  
Admitted.