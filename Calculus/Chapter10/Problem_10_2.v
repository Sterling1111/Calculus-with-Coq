From Calculus.Chapter10 Require Import Prelude.

Set Ltac Profiling.

Lemma lemma_10_2_i : ⟦ der ⟧ (λ x, sin ((x + 1)^2 * (x+2))) = 
  (λ x, cos ((x + 1)^2 * (x + 2)) * (2 * (x + 1) * (x + 2) + (x + 1)^2)).
Proof.
  auto_diff.
Qed.

Lemma lemma_10_2_ii : ⟦ der ⟧ (λ x, (sin (x^2 + sin x))^3) = 
  (λ x, 3 * (sin (x^2 + sin x))^2 * cos (x^2 + sin x) * (2 * x + cos x)).
Proof. auto_diff. Qed.

Lemma lemma_10_2_iii : ⟦ der ⟧ (λ x, (sin ((x + sin x)^2))^2) = 
  (λ x, 2 * sin ((x + sin x)^2) * cos ((x + sin x)^2) * (2 * (x + sin x) * (1 + cos x))).
Proof. auto_diff. Qed.

Lemma lemma_10_2_iv :
  ∀ x, cos (x^3) ≠ 0 -> ⟦ der x ⟧ (λ x, sin (x^3 / cos (x^3))) = 
    (λ x, cos (x^3 / cos (x^3)) * ((3 * x^2 * cos (x^3) + x^3 * sin (x^3) * 3 * x^2) / (cos (x^3))^2)).
Proof.
  auto_diff. 
Qed.

Lemma lemma_10_2_v : ⟦ der ⟧ (λ x, sin (x * sin x) + sin (sin (x^2))) = 
  (λ x, cos (x * sin x) * (sin x + x * cos x) + cos (sin (x^2)) * cos (x^2) * 2 * x).
Proof. auto_diff. Qed.

Lemma lemma_10_2_vi : ⟦ der ⟧ (λ x, (cos x)^(31^2)) = 
  (λ x, (31^2) * cos x^(31^2 - 1) * (- sin x)).
Proof.
  auto_diff.
Qed.

Lemma lemma_10_2_vii : ⟦ der ⟧ (λ x, (sin x)^2 * sin (x^2) * (sin (x^2))^2) = 
  (λ x, (2 * sin x * cos x) * sin (x^2) * (sin (x^2))^2 + 
        (sin x)^2 * (cos (x^2) * 2 * x) * (sin (x^2))^2 + 
        (sin x)^2 * sin (x^2) * (2 * sin (x^2) * cos (x^2) * 2 * x)).
Proof. auto_diff. Qed.

Lemma lemma_10_2_viii : ⟦ der ⟧ (λ x, (sin ( (sin (sin x))^2 ))^3) = 
  (λ x, 3 * (sin ((sin (sin x))^2))^2 * cos ((sin (sin x))^2) * (2 * sin (sin x) * cos (sin x) * cos x)).
Proof. auto_diff. Qed.

Lemma lemma_10_2_ix : ⟦ der ⟧ (λ x, (x + (sin x)^5)^6) = 
  (λ x, 6 * (x + (sin x)^5)^5 * (1 + 5 * (sin x)^4 * cos x)).
Proof. auto_diff. Qed.

Lemma lemma_10_2_x : ⟦ der ⟧ (λ x, sin (sin (sin (sin (sin x))))) = 
  (λ x, cos (sin (sin (sin (sin x)))) * cos (sin (sin (sin x))) * cos (sin (sin x)) * cos (sin x) * cos x).
Proof. auto_diff. Qed.

Lemma lemma_10_2_xi : ⟦ der ⟧ (λ x, sin (((sin x)^7 * x^7 + 1)^7)) = 
  (λ x, cos (((sin x)^7 * x^7 + 1)^7) * (7 * ((sin x)^7 * x^7 + 1)^6 * (7 * (sin x)^6 * cos x * x^7 + (sin x)^7 * 7 * x^6))).
Proof. auto_diff. Qed.

Lemma lemma_10_2_xii : ⟦ der ⟧ (λ x, ((((x^2 + x)^3 + x)^4 + x)^5)) = 
  (λ x, 5 * (((x^2 + x)^3 + x)^4 + x)^4 * (4 * ((x^2 + x)^3 + x)^3 * (3 * (x^2 + x)^2 * (2 * x + 1) + 1) + 1)).
Proof. auto_diff. Qed.

Lemma lemma_10_2_xiii : ⟦ der ⟧ (λ x, sin (x^2 + sin (x^2 + sin (x^2)))) = 
  (λ x, cos (x^2 + sin (x^2 + sin (x^2))) * (2 * x + cos (x^2 + sin (x^2)) * (2 * x + cos (x^2) * 2 * x))).
Proof. auto_diff. Qed.

Lemma lemma_10_2_xiv : ⟦ der ⟧ (λ x, sin (6 * cos (6 * sin (6 * cos (6 * x))))) = 
  (λ x, cos (6 * cos (6 * sin (6 * cos (6 * x)))) * (-6 * sin (6 * sin (6 * cos (6 * x)))) * (6 * cos (6 * cos (6 * x))) * (-6 * sin (6 * x)) * 6).
Proof. auto_diff. Qed.

Lemma lemma_10_2_xv : ∀ x, 1 + sin x ≠ 0 -> ⟦ der x ⟧ (λ x, (sin (x^2) * (sin x)^2) / (1 + sin x)) = 
  (λ x, ((cos (x^2) * 2 * x * (sin x)^2 + sin (x^2) * 2 * sin x * cos x) * (1 + sin x) - 
        (sin (x^2) * (sin x)^2 * cos x)) / (1 + sin x)^2).
Proof. auto_diff. Qed. 

Lemma lemma_10_2_xvi : ∀ x, x + sin x ≠ 0 -> x - 2 / (x + sin x) ≠ 0 -> ⟦ der x ⟧ (λ x, 1 / (x - 2 / (x + sin x))) = 
  (λ x, - (1 - (-2 * (1 + cos x) / (x + sin x)^2)) / (x - 2 / (x + sin x))^2).
Proof. auto_diff. Qed.

Lemma lemma_10_2_xvii : ∀ x, sin x ≠ 0 -> sin (x^3 / sin x) ≠ 0 -> ⟦ der x ⟧ (λ x, sin (x^3 / sin (x^3 / sin x))) = 
  (λ x, cos (x^3 / sin (x^3 / sin x)) * ((3 * x^2 * sin (x^3 / sin x) - x^3 * cos (x^3 / sin x) * ((3 * x^2 * sin x - x^3 * cos x) / (sin x)^2)) / (sin (x^3 / sin x))^2)).
Proof.
  auto_diff.
Qed.

Lemma lemma_10_2_xviii : ∀ x, x - sin x ≠ 0 -> x - sin (x / (x - sin x)) ≠ 0 -> ⟦ der x ⟧ (λ x, sin (x / (x - sin (x / (x - sin x))))) = 
  let f := (λ x, (x - sin (x / (x - sin x)))) in
        λ x, cos (x / f x) * ((f x - x * (1 - cos (x / (x - sin x)) * ((x - sin x - x * (1 - cos x)) / (x - sin x)^2))) / (f x)^2).
Proof. auto_diff. Qed.

Show Ltac Profile.