From Calculus.Chapter10 Require Import Prelude.

Set Ltac Profiling.

Lemma lemma_10_1_i : ⟦ der ⟧ (λ x, sin (x + x^2)) = (λ x, cos (x + x^2) * (1 + 2 * x)).
Proof.
  set (f := λ x, sin x).
  set (f' := λ x, cos x).
  set (g := λ x, x + x^2).
  set (g' := λ x, 1 + 2 * x).

  replace (λ x, f (x + x^2)) with (f ∘ g) by reflexivity.
  replace (λ x : ℝ, f' (x + x ^ 2) * (1 + 2 * x)) with ((f' ∘ g) ∙ g') by reflexivity.
  
  assert (H1 : ⟦ der ⟧ f = f') by apply sin_derivative.
  assert (H2 : ⟦ der ⟧ g = g').
  {
    unfold g, g'.
    apply theorem_10_3_b. apply theorem_10_2. replace (Rmult 2) with (fun x => INR 2 * x^(2-1)).
    2 : { extensionality x. simpl. lra. } apply power_rule.
  }
  apply chain_rule; auto.
Qed.

Lemma lemma_10_1_i' : ⟦ der ⟧ (λ x, sin (x + x^2)) = (λ x, cos (x + x^2) * (1 + 2 * x)).
Proof. auto_diff. Qed.

Lemma lemma_10_1_ii : ⟦ der ⟧ (λ x, sin x + sin (x^2)) = (λ x, cos x + cos (x^2) * (2 * x)).
Proof. auto_diff. Qed.

Lemma lemma_10_1_iii : ⟦ der ⟧ (λ x, sin (cos x)) = (λ x, cos (cos x) * (- sin x)).
Proof. auto_diff. Qed.

Lemma lemma_10_1_iv : ⟦ der ⟧ (λ x, sin (sin x)) = (λ x, cos (sin x) * cos x).
Proof. auto_diff. Qed.

Lemma lemma_10_1_v : ∀ x, x ≠ 0 -> ⟦ der x ⟧ (λ x, sin (cos x / x)) = (λ x, cos (cos x / x) * ((- x * sin x - cos x) / x^2)).
Proof. auto_diff. Qed.

Lemma lemma_10_1_vi : ∀ x, x ≠ 0 -> ⟦ der x ⟧ (λ x, sin (cos x) / x) = (λ x, (- x * sin x * cos (cos x) - sin (cos x)) / x^2).
Proof. auto_diff. Qed.

Lemma lemma_10_1_vii : ⟦ der ⟧ (λ x, sin (x + sin x)) = (λ x, cos (x + sin x) * (1 + cos x)).
Proof. auto_diff. Qed.

Lemma lemma_10_1_viii : ⟦ der ⟧ (λ x, sin (cos (sin x))) = (λ x, cos (cos (sin x)) * (- sin (sin x) * cos x)).
Proof. auto_diff. Qed.

Show Ltac Profile.