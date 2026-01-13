From Lib Require Import Imports Polynomial Exponential.
Open Scope R_scope.

Definition algebraic (x : R) : Prop :=
  exists l : list R,
    Forall (fun c => exists z : Z, c = IZR z) l /\
    leading_coefficient l <> 0 /\
    polynomial l x = 0.

Definition transcendental (x : R) : Prop :=
  ~ algebraic x.

Lemma transcendental_e : transcendental e.
Proof.
  intros [l [H1 [H2 H3]]]. rewrite Forall_forall in H1.
  (* good luck *)
Admitted.