From Lib Require Import Imports Sets Notations Functions Sums Complex Sequence Series Limit ComplexLimit ComplexSequence.
Import SetNotations FunctionNotations LimitNotations SequenceNotations SumNotations SeriesNotations.

Open Scope C_scope.
Open Scope R_scope.

Fixpoint Csum_f_R0 (a : nat -> C) (n : nat) : C :=
  match n with
  | 0%nat => a 0%nat
  | S k => (Csum_f_R0 a k + a (S k))%C
  end.

Definition Cpartial_sum (a : Csequence) (n : nat) := Csum_f_R0 a n.

Definition Cseries_sum (a : Csequence) (L : C) : Prop :=
  ⟦ lim ⟧ (Cpartial_sum a) = L.

Definition Cseries_converges (a : Csequence) : Prop :=
  Cconvergent_sequence (Cpartial_sum a).

Definition Cseries_converges_absolutely (a : Csequence) : Prop :=
  series_converges (fun n => Cnorm (a n)).

Theorem Cseries_converges_component_iff : forall (a : Csequence),
  let b := fun n => fst (a n) in
  let c := fun n => snd (a n) in
  Cseries_converges a <-> (series_converges b /\ series_converges c).
Proof.
Admitted.

Theorem Cseries_converges_absolutely_component_iff : forall (a : Csequence),
  let b := fun n => fst (a n) in
  let c := fun n => snd (a n) in
  Cseries_converges_absolutely a <-> (series_converges_absolutely b /\ series_converges_absolutely c).
Proof.
Admitted.
