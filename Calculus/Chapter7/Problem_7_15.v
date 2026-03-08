From Calculus.Chapter7 Require Import Prelude.

Definition limit_pos_infty (f : R -> R) (L : R) :=
  forall ε, ε > 0 -> exists M, forall x, x > M -> | f x - L | < ε.

Definition limit_neg_infty (f : R -> R) (L : R) :=
  forall ε, ε > 0 -> exists M, forall x, x < M -> | f x - L | < ε.

Lemma lemma_7_15_a : forall ϕ n,
  continuous ϕ ->
  (exists k, n = (2 * k + 1)%nat) ->
  limit_pos_infty (fun x => ϕ x / x^(n)) 0 ->
  limit_neg_infty (fun x => ϕ x / x^(n)) 0 ->
  exists x, x^(n) + ϕ x = 0.
Proof. Admitted.

Lemma lemma_7_15_b : forall ϕ n,
  continuous ϕ ->
  (exists k, n = (2 * k)%nat) ->
  limit_pos_infty (fun x => ϕ x / x^(n)) 0 ->
  limit_neg_infty (fun x => ϕ x / x^(n)) 0 ->
  exists y, forall x, y^(n) + ϕ y <= x^(n) + ϕ x.
Proof. Admitted.
