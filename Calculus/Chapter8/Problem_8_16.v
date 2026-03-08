From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_16_helper : forall f a b,
  continuous_on f [a, b] ->
  ~ has_upper_bound (fun y => exists x, x ∈ [a, b] /\ y = f x) ->
  ~ has_upper_bound (fun y => exists x, x ∈ [a, (a+b)/2] /\ y = f x) \/
  ~ has_upper_bound (fun y => exists x, x ∈ [(a+b)/2, b] /\ y = f x).
Proof. Admitted.
