From Calculus.Chapter8 Require Import Prelude.

Definition almost_upper_bound (A : Ensemble ℝ) (x : ℝ) :=
  Finite_set (fun y => y ∈ A /\ y >= x).

Definition almost_lower_bound (A : Ensemble ℝ) (x : ℝ) :=
  Finite_set (fun y => y ∈ A /\ y <= x).

Lemma lemma_8_18_b_1 : forall A,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  (fun x => almost_upper_bound A x) ≠ ∅.
Proof. Admitted.

Lemma lemma_8_18_b_2 : forall A,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  has_lower_bound (fun x => almost_upper_bound A x).
Proof. Admitted.

Definition lim_sup (A : Ensemble ℝ) (l : ℝ) :=
  is_glb (fun x => almost_upper_bound A x) l.

Lemma lemma_8_18_c : forall A l,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  lim_sup A l -> True.
Proof. Admitted.
