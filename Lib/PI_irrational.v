From Lib Require Import Imports Notations Integral Derivative Functions Continuity Limit Sets Reals_util Inverse Trigonometry Sums Rational.
Import IntervalNotations SetNotations Function_Notations DerivativeNotations LimitNotations.

Open Scope R_scope.

Definition f_n n x :=
  (x^n * (1 - x)^n) / n!.

Lemma f_n_bounds : ∀ n x,
  0 < x < 1 ->
  0 < f_n n x < 1 / n!.
Proof.
Admitted.

Lemma f_n_is_polynomial : ∀ n, ∃ c,
  forall x, f_n n x = (1 / n!) * ∑ n (2*n) (λ i, (nth i c 0%Z) * x^i).
Proof.
Admitted.

Lemma f_n_derivatives_at_0_are_integers : ∀ (n k: nat) (r : R),
  ⟦ der ^ k 0 ⟧ (f_n n) = r -> is_integer r.
Proof.
Admitted.

Lemma f_n_symmetry : ∀ n x,
  f_n n x = f_n n (1 - x).
Proof.
  intros n x. unfold f_n. replace (1 - (1 - x)) with x by nra. lra.
Qed.

Lemma f_n_derivative_symmetry : ∀ f_n' (n k: nat) (x : R),
  ⟦ der ^ k ⟧ (f_n n) = f_n' ->
  ⟦ der ^ k x ⟧ (f_n n) = ((-1) ^ k) * f_n' (1 - x).
Proof.
Admitted.

Lemma f_n_derivatives_at_1_are_integers : ∀ (n k: nat) (r : R),
  ⟦ der ^ k 1 ⟧ (f_n n) = r -> is_integer r.
Proof.
Admitted.

Lemma pow_over_factorial_tends_to_0 : ∀ x ε,
  x > 0 -> ε > 0 -> ∃ n, x^n / n! < ε.
Proof.
Admitted.

Theorem theorem_16_1 : irrational π.
Proof.
  apply irrational_square_imp_irrational. intros [a [b H1]].
  Set Printing Coercions.
  assert (a > 0 /\ b > 0) as [H2 H3] by admit.



Admitted.