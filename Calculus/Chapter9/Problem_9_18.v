From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_18 : forall f a,
  (forall x, ~ rational x -> f x = 0) ->
  (forall x p q, (q > 0)%Z -> x = IZR p / IZR q -> 
    (forall p' q', (q' > 0)%Z -> x = IZR p' / IZR q' -> (q <= q')%Z) -> 
    f x = 1 / IZR q) ->
  ~ differentiable_at f a.
Proof.
Admitted.