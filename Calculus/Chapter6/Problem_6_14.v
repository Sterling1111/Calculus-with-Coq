From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_14_a : forall f g h a,
  continuous_at g a -> continuous_at h a -> g a = h a ->
  (forall x, x >= a -> f x = g x) ->
  (forall x, x <= a -> f x = h x) ->
  continuous_at f a.
Proof.
  intros f g h a H1 H2 H3 H4 H5. intros ε H6.
  destruct (H1 ε H6) as [δ1 [H7 H8]]. destruct (H2 ε H6) as [δ2 [H9 H10]].
  exists (Rmin δ1 δ2). split; [solve_R|]. intros x H11.
  assert (x = a \/ x > a \/ x < a) as [H12 | [H12 | H12]] by lra.
  - rewrite H12, H4; [|lra]. assert (g a - f a = 0) by (rewrite H4; lra). solve_R.
  - rewrite H4 by lra. assert (f a = g a) by (rewrite H4; lra). rewrite H.
    specialize (H8 x). assert (0 < |x - a| < δ1) by solve_R. apply H8 in H0. solve_R.
  - rewrite H5 by lra. assert (f a = h a) by (rewrite H5; lra). rewrite H.
    specialize (H10 x). assert (0 < |x - a| < δ2) by solve_R. apply H10 in H0. solve_R.
Qed.

Lemma lemma_6_14_b : forall f g h a b c,
  a < b -> b < c ->
  continuous_on g [a, b] -> continuous_on h [b, c] ->
  g b = h b ->
  (forall x, x ∈ [a, b] -> f x = g x) ->
  (forall x, x ∈ [b, c] -> f x = h x) ->
  continuous_on f [a, c].
Proof. Admitted.
