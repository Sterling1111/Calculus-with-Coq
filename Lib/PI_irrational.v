From Lib Require Import Imports Notations Integral Derivative Functions Continuity Limit Sets Reals_util Inverse Trigonometry Sums Rational.
Import IntervalNotations SetNotations Function_Notations DerivativeNotations LimitNotations.

Open Scope R_scope.

Local Definition f n x :=
  (x^n * (1 - x)^n) / n!.

Lemma f_bounds : ∀ n x,
  0 < x < 1 ->
  0 < f n x < 1 / n!.
Proof.
Admitted.

Lemma f_is_polynomial : ∀ n, ∃ c,
  forall x, f n x = (1 / n!) * ∑ n (2*n) (λ i, (nth i c 0%Z) * x^i).
Proof.
Admitted.

Lemma f_derivatives_at_0_are_integers : ∀ (n k: nat) (r : R),
  ⟦ der ^ k 0 ⟧ (f n) = r -> is_integer r.
Proof.
Admitted.

Lemma f_symmetry : ∀ n x,
  f n x = f n (1 - x).
Proof.
  intros n x. unfold f. replace (1 - (1 - x)) with x by nra. lra.
Qed.

Lemma f_derivative_symmetry : ∀ f_n' (n k: nat) (x : R),
  ⟦ der ^ k ⟧ (f n) = f_n' ->
  ⟦ der ^ k x ⟧ (f n) = ((-1) ^ k) * f_n' (1 - x).
Proof.
Admitted.

Lemma f_derivatives_at_1_are_integers : ∀ (n k: nat) (r : R),
  ⟦ der ^ k 1 ⟧ (f n) = r -> is_integer r.
Proof.
Admitted.

Lemma pow_over_factorial_tends_to_0 : ∀ x ε,
  x > 0 -> ε > 0 -> ∃ n, x^n / n! < ε.
Proof.
Admitted.

Theorem theorem_16_1 : irrational π.
Proof.
  apply irrational_square_imp_irrational. intros [a [b H1]].
  assert (a > 0 /\ b > 0) as [H2 H3] by admit.
  assert (H4 : forall n, is_integer (π * ∫ 0 1 (λ x, a^n * f n x * sin (π * x)))).
  {
    intros n.
    set (G := λ x, b^n * ∑ 0 n (λ k, (-1)^k * π^(2*n - 2*k) * (⟦ Der ^ (2*k) x ⟧ (f n)))).
    set (G' := λ x, b^n * ∑ 0 n (λ k, (-1)^k * π^(2*n - 2*k) * (⟦ Der ^ (2*k + 1) x ⟧ (f n)))).
    set (G'' := λ x, b^n * ∑ 0 n (λ k, (-1)^k * π^(2*n - 2*k) * (⟦ Der ^ (2*k + 2) x ⟧ (f n)))).
    set (H := λ x, (G' x) * sin (π*x) - π * ((G x) * cos (π*x))).
    set (H' := λ x, ((G'' x) * sin (π*x) + G'(x) * π * cos (π*x)) - (π * ((G' x) * cos (π*x) - π * (G x) * sin (π*x)))).

    assert (H4 : is_integer (G 0)) by admit.
    assert (H5 : is_integer (G 1)) by admit.
    assert (H6 : ⟦ der ⟧ G = G') by admit.
    assert (H7 : ⟦ der ⟧ G' = G'') by admit.
    
    assert (H8 : ⟦ der ⟧ H = H').
    {
      unfold H, H'.
      assert (H8 : ⟦ der ⟧ (fun x => sin (π*x)) = fun x => π * cos (π*x)) by admit.
      assert (H9 : ⟦ der ⟧ (fun x => cos (π*x)) = fun x => - π * sin (π*x)) by admit.
      
      apply theorem_10_3_d.
      - pose proof theorem_10_4_c G' (fun x => sin (π*x)) G'' (fun x => π * cos (π*x)) H7 H8 as H10.
        admit.
      - apply theorem_10_5'. 
        pose proof theorem_10_4_c G (fun x => cos (π*x)) G' (fun x => - π * sin (π*x)) H6 H9 as H11.
        admit.
    }
    assert (H9 : H' = (fun x => π^2 * (a^n * f n x * sin (π * x)))).
    {
      unfold H'. extensionality x. assert (H9 : G'' x + π^2 * (G x) = π^2 * a^n * f n x) by admit.
      nra.
    }
    assert (H10 : ∫ 0 1 (λ x : ℝ, π ^ 2 * (a ^ n * f n x * sin (π * x))) = H 1 - H 0).
    {
      rewrite <- H9.
      apply FTC2.
      - lra.
      - admit.
      - apply derivative_imp_derivative_on; try lra; auto.
    }
    assert (H11 : H 1 - H 0 = π * (G 1 + G 0)).
    { unfold H. rewrite Rmult_1_r, Rmult_0_r. rewrite sin_0, sin_π, cos_0, cos_π. lra. }

    rewrite H11 in H10. rewrite theorem_13_6_b in H10; try lra.
    2 : { apply theorem_13_3; try lra. admit. }
    pose proof π_pos as H12.
    apply Rmult_eq_compat_r with (r := 1 / π) in H10; try lra. field_simplify in H10; try lra.
    rewrite H10.
    apply is_integer_plus; auto.
  }
Admitted.