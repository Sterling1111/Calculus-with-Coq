From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_13_a : forall f a b,
  a < b -> continuous_on f [a, b] -> exists g,
    (forall x, x ∈ [a, b] -> g x = f x) /\ continuous_on g ℝ.
Proof.
  intros f a b H1 H2.
  set (g := fun x => if Rle_dec x a then f a else if Rle_dec x b then f x else f b).
  exists g. split.
  - intros x H3. unfold g. destruct (Rle_dec x a) as [H4 | H4]; solve_R. replace x with a by solve_R. reflexivity.
  - intros x H3. assert (x < a \/ x ∈ [a, b] \/ x > b) as [H4 | [H4 | H4]] by solve_R.
Admitted.