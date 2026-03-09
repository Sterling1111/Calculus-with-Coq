From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_39 : forall f g a b,
  a < b ->
  integrable_on a b f ->
  integrable_on a b g ->
  (∫ a b (f ⋅ g))^2 <= (∫ a b (fun x => (f x)^2)) * (∫ a b (fun x => (g x)^2)).
Admitted.
