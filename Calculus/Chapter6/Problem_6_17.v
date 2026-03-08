From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_17_b : forall f g a l,
  ⟦ lim a ⟧ f = l ->
  l <> f a ->
  (forall x, x <> a -> g x = f x) ->
  g a = l ->
  continuous_at g a.
Proof.
  intros f g a l H1 H2 H3 H4. unfold continuous_at.
  rewrite H4. apply limit_eq with (f1 := f).
  - exists 1. split; [solve_R | intros x H5].
    rewrite H3; [reflexivity|solve_R].
  - exact H1.
Qed.

Lemma lemma_6_17_d : forall f g,
  (forall x, exists l, ⟦ lim x ⟧ f = l) ->
  (forall x, ⟦ lim x ⟧ f = g x) ->
  continuous g.
Proof. Admitted.
