From Lib Require Import Imports Sets Limit Continuity Derivative Notations Reals_util Inverse.
Import LimitNotations IntervalNotations SetNotations DerivativeNotations Function_Notations.
Open Scope R_scope.

Lemma lemma_12_24_a : forall f f_inv, 
  continuous f -> inverse f f_inv -> exists x, f x = x.
Proof.
  intros f f_inv H1 H2. pose proof exists_inverse_iff f as H3.
  assert (H4 : exists f_inv, inverse f f_inv) by (exists f_inv; auto).
  apply H3 in H4 as [H4 _]. 
Admitted.