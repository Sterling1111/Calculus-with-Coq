From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_64 : forall f f',
  f 0 = 0 ->
  ⟦ der ⟧ f = f' ->
  increasing f' ->
  increasing_on (fun x => f x / x) (0, ∞).
Admitted.
