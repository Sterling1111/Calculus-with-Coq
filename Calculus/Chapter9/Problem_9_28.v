From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_28_a : forall f f' f'' x,
  f = (fun x => (| x |)^3) -> 
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ f' = f'' -> 
  f' x = 3 * x * | x | /\ f'' x = 6 * | x |.
Proof.
Admitted.

Lemma lemma_9_28_b : forall f f' f'' x,
  (forall x, x >= 0 -> f x = x^4) ->
  (forall x, x <= 0 -> f x = -x^4) ->
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ f' = f'' -> 
  f' x = 4 * (| x |) ^ 3 /\ f'' x = 12 * x * | x |.
Proof.
Admitted.
