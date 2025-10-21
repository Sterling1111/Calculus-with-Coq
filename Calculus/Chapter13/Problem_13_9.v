From Lib Require Import Imports Sets Limit Continuity Derivative Integral Notations Reals_util.
Import LimitNotations IntervalNotations SetNotations DerivativeNotations.
Open Scope R_scope.

Lemma lemma_13_9 : ∀ a b c d f g,
    a <= b -> c <= d -> integrable_on a b f -> integrable_on c d g ->
      ∫ a b (λ x, ∫ c d (λ y, f x * g y)) = (∫ a b f) * (∫ c d g).
Proof.
  intros a b c d f g H1 H2 H3 H4.

Admitted.