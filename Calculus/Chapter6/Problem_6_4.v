From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_4 :
  exists f, (forall x, ~ continuous_at f x) /\ continuous (fun x => |f x|).
Proof. Admitted.
