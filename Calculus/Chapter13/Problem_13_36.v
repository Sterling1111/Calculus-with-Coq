From Calculus.Chapter13 Require Import Prelude.

Lemma lemma_13_36_b : forall f a b,
  a < b ->
  integrable_on a b f ->
  integrable_on a b (fun x => |f x|).
Admitted.

Lemma lemma_13_36_c : forall f g a b,
  a < b ->
  integrable_on a b f ->
  integrable_on a b g ->
  integrable_on a b (fun x => Rmax (f x) (g x)) /\
  integrable_on a b (fun x => Rmin (f x) (g x)).
Admitted.
