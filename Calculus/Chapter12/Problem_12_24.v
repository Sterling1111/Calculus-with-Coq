From Lib Require Import Imports Sets Limit Continuity Derivative Notations Reals_util Inverse Functions Interval.
Import LimitNotations IntervalNotations SetNotations DerivativeNotations FunctionNotations.
Open Scope R_scope.

Lemma lemma_12_24_a : forall f f_inv, 
  continuous f -> inverse f f_inv -> exists x, f x = x.
Proof.
  intros f f_inv H1 H2. 
Admitted.