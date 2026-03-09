From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_23_a_helper : forall f g a b,
  increasing f -> decreasing g -> f a = g a -> f b = g b -> a = b.
Proof.
  intros f g a b H1 H2 H3 H4.
  specialize (H1 (Rmin a b) (Rmax a b) ltac:(apply Full_intro) ltac:(apply Full_intro)).
  specialize (H2 (Rmin a b) (Rmax a b) ltac:(apply Full_intro) ltac:(apply Full_intro)).
  pose proof Rtotal_order a b as [H5 | [H5 | H5]]; solve_R.
Qed.

Lemma lemma_12_23_a : forall f g,
  increasing f ->
  decreasing g ->
  (exists x, f x = g x) ->
  exists! x, f x = g x.
Admitted.