From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_11 : forall f g a l m,
  ⟦ lim a ⟧ f = l -> ⟦ lim a ⟧ g = m -> m <> 0 ->
  ⟦ lim a ⟧ (fun x => f x / g x) = l / m.
Proof.
  intros f g a l m H1 H2 H3. apply (limit_div f g a l m H1 H2 H3).
Qed.