From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_10 : forall a b f g,
  a < b -> continuous_on f [a, b] -> continuous_on g [a, b] ->
  f a < g a -> f b > g b ->
  exists x, x ∈ [a, b] /\ f x = g x.
Proof.
  intros a b f g H1 H2 H3 H4 H5.
  set (h := (f - g)%function).
  assert (H6 : continuous_on h [a, b]). 
  {
    unfold h. intros x H6. specialize (H2 x H6).
    specialize (H3 x H6). apply limit_on_minus; auto. 
  }
  assert (h a < 0 < h b) as H7 by (unfold h; lra).
  pose proof intermediate_value_theorem h a b 0 H1 H6 H7 as [x [H9 H10]].
  exists x. split; auto. unfold h in H10. lra.
Qed.