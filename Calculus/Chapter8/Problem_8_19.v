From Calculus.Chapter8 Require Import Prelude.
Require Import Problem_8_18.

Definition lim_inf (A : Ensemble ℝ) (l : ℝ) :=
  is_lub (fun x => almost_lower_bound A x) l.

Lemma lemma_8_19_a : forall A li ls,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  lim_inf A li -> lim_sup A ls -> li <= ls.
Proof. Admitted.

Lemma lemma_8_19_b : forall A ls supa,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  lim_sup A ls -> is_lub A supa -> ls <= supa.
Proof. Admitted.

Lemma lemma_8_19_c : forall A ls supa,
  Infinite_set A -> has_upper_bound A -> has_lower_bound A ->
  lim_sup A ls -> is_lub A supa -> ls < supa ->
  supa ∈ A.
Proof. Admitted.
