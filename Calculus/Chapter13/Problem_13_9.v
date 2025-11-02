From Lib Require Import Imports Sets Limit Continuity Derivative Integral Notations Reals_util.
Import LimitNotations IntervalNotations SetNotations DerivativeNotations Function_Notations.
Open Scope R_scope.

Lemma lemma_13_9 : ∀ a b c d f g,
    a < b -> c < d -> integrable_on a b f -> integrable_on c d g ->
      ∫ a b (λ x, ∫ c d (f x * g)) = (∫ a b f) * (∫ c d g).
Proof.
  intros a b c d f g H1 H2 H3 H4. 
  replace ((λ x : ℝ, ∫ c d (λ y : ℝ, f x * g y))) with (λ x : ℝ, (∫ c d g) * f x).
  2 : { extensionality x. rewrite theorem_13_6_b with (c := f x); solve_R. }
  rewrite theorem_13_6_b; solve_R.
Qed.