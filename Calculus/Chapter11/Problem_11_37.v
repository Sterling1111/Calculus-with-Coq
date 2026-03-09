(* problem 11 37 *)
From Calculus.Chapter11 Require Import Prelude.

Definition lipschitz_order (f : R -> R) (alpha : R) (D : Ensemble R) :=
  exists C, C > 0 /\ forall x y, x ∈ D -> y ∈ D -> |f x - f y| <= C * (|x - y| ^^ alpha).

Lemma lemma_11_37_a : forall f alpha a δ,
  alpha > 0 -> δ > 0 ->
  lipschitz_order f alpha (a - δ, a + δ) ->
  continuous_at f a.
Admitted.

Lemma lemma_11_37_b : forall f alpha D,
  alpha > 0 ->
  lipschitz_order f alpha D ->
  uniformly_continuous_on f D.
Admitted.

Lemma lemma_11_37_e : forall f alpha a b,
  a < b ->
  alpha > 1 ->
  lipschitz_order f alpha [a, b] ->
  exists c, forall x, x ∈ [a, b] -> f x = c.
Admitted.