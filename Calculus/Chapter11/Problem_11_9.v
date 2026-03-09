From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_9 : forall f f' x,
  ⟦ der x ⟧ f = f' ->
  (⟦ der x ⟧ (fun y => (f y)^2) = (fun _ => 0) <-> f' x = 0 \/ f x = 0).
Admitted.
