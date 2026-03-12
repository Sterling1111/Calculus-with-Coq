From Lib Require Import Imports Sets Notations Functions Complex Limit Continuity ComplexLimit.
Import SetNotations FunctionNotations LimitNotations C_LimitNotations.

Open Scope C_scope.
Open Scope R_scope.

Definition continuous_c_at (f : C -> C) (a : C) : Prop :=
  ⟦ lim a ⟧ f = f a.

Definition continuous_c_on (f : C -> C) (D : Ensemble C) : Prop :=
  forall a, a ∈ D -> continuous_c_at f a.

Definition continuous_c (f : C -> C) : Prop :=
  forall a, continuous_c_at f a.

Theorem continuous_c_component_iff : forall (f : C -> C) (a : C),
  let u := fun z => fst (f z) in
  let v := fun z => snd (f z) in
  continuous_c_at f a <->
  (⟦ lim a ⟧ u = fst (f a) /\ ⟦ lim a ⟧ v = snd (f a))%R.
Proof.
  intros f a u v. unfold continuous_c_at.
  apply limit_c_component_iff_clean.
Qed.
