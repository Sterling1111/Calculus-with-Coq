From Calculus.Chapter7 Require Import Prelude.

Definition limit_pos_infty (f : R -> R) (L : R) :=
  forall ε, ε > 0 -> exists M, forall x, x > M -> | f x - L | < ε.

Definition limit_neg_infty (f : R -> R) (L : R) :=
  forall ε, ε > 0 -> exists M, forall x, x < M -> | f x - L | < ε.

Lemma lemma_7_18 : forall f,
  continuous f ->
  (forall x, f x > 0) ->
  limit_pos_infty f 0 ->
  limit_neg_infty f 0 ->
  exists y, forall x, f y >= f x.
Proof. Admitted.
