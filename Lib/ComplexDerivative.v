From Lib Require Import Imports Sets Notations Functions Complex Limit Derivative ComplexLimit ComplexContinuity.
Import SetNotations FunctionNotations LimitNotations DerivativeNotations C_LimitNotations.

Open Scope C_scope.
Open Scope R_scope.

Definition differentiable_c_at (f : C -> C) (a : C) :=
  exists L : C, (⟦ lim 0 ⟧ (fun h : C => (f (a + h) - f a) / h) = L)%C.

Definition derivative_c_at (f f' : C -> C) (a : C) :=
  (⟦ lim 0 ⟧ (fun h : C => (f (a + h) - f a) / h) = f' a)%C.

Definition derivative_c (f f' : C -> C) :=
  forall x, derivative_c_at f f' x.

Definition differentiable_c (f : C -> C) :=
  forall x, differentiable_c_at f x.

Lemma derivative_c_at_imp_continuous_c_at : forall f f' a,
  derivative_c_at f f' a -> continuous_c_at f a.
Proof.
Admitted.
