From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_37 : forall f a b,
  a < b ->
  integrable_on a b f ->
  |∫ a b f| <= ∫ a b (fun x => |f x|).
Admitted.
