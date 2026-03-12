From Lib Require Import Imports Sets Notations Functions Complex Sequence Limit ComplexLimit.
Import SetNotations FunctionNotations LimitNotations SequenceNotations.

Open Scope C_scope.
Open Scope R_scope.

Definition Csequence := nat -> C.

Definition Cseq_limit (a : Csequence) (L : C) :=
  forall ε, ε > 0 ->
    exists N, forall n : nat, (n > N)%nat -> Cnorm (a n - L)%C < ε.

Notation "⟦ 'lim' ⟧ a '=' L" := 
    (Cseq_limit a L)
      (at level 70, a at level 0, no associativity, format "⟦  'lim'  ⟧  a  '='  L") : C_scope.

Definition Cconvergent_sequence (a : Csequence) :=
  exists L, ⟦ lim ⟧ a = L.

Definition Ccauchy_sequence (a : Csequence) : Prop :=
  forall ε, ε > 0 ->
    exists N, forall n m : nat,
      (n > N)%nat -> (m > N)%nat -> Cnorm (a n - a m)%C < ε.

Theorem Cseq_limit_component_iff : forall (a : Csequence) (L : C),
  let b := fun n => fst (a n) in
  let c := fun n => snd (a n) in
  ⟦ lim ⟧ a = L <-> (⟦ lim ⟧ b = fst L /\ ⟦ lim ⟧ c = snd L)%R.
Proof.
Admitted.
