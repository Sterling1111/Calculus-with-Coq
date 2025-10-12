From Lib Require Import Imports Notations Reals_util.
Open Scope R_scope.

Lemma lemma_1_18_a : forall b c x,
  (b^2 - 4 * c >= 0) -> ((x = (-b + √ (b^2 - 4 * c))/ 2 \/ x = (-b - √ (b^2 - 4 * c))/ 2)) -> x^2 + b * x + c = 0.
Proof.
  intros b c x H1 [H2 | H2].
  - rewrite H2. replace (((- b + √ (b ^ 2 - 4 * c)) / 2) ^ 2) with ((b^2 - 2 * b * √ (b^2 - 4 * c) + (√ (b^2 - 4 * c))^2) / 4) by nra.
    simpl. repeat rewrite Rmult_1_r. rewrite sqrt_sqrt. 2 : { lra. } nra.
  - rewrite H2. replace (((- b - √ (b ^ 2 - 4 * c)) / 2) ^ 2) with ((b^2 + 2 * b * √ (b^2 - 4 * c) + (√ (b^2 - 4 * c))^2) / 4) by nra.
    simpl. repeat rewrite Rmult_1_r. rewrite sqrt_sqrt. 2 : { lra. } nra.
Qed.

Lemma lemma_1_18_a' : forall b c,
  b^2 - 4 * c >= 0 -> (exists x, x^2 + b * x + c = 0).
Proof.
  intros b c H1.
  exists ((-b + √ (b^2 - 4 * c)) / 2).
  apply lemma_1_18_a; auto.
Qed.

Lemma lemma_1_18_a'' : forall b c,
  (forall x, x^2 + b * x + c <> 0) -> b^2 - 4 * c < 0.
Proof.
  intros b c H1.
  assert (H2 : b^2 - 4 * c >= 0 \/ b^2 - 4 * c < 0) by nra. destruct H2 as [H2 | H2].
  - exfalso. apply lemma_1_18_a' in H2. destruct H2 as [x H2]. unfold not in H1. specialize (H1 x). 
    apply H1. apply H2.
  - apply H2.
Qed.

Lemma lemma_1_18_b : forall b c x,
  (b^2 - 4 * c < 0) -> x^2 + b * x + c > 0.
Proof.
  intros b c x H1. replace (x^2 + b * x + c) with ((x + b / 2)^2 + (c - b^2 / 4)) by nra.
  assert (H2 : (x + b / 2)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
  assert (H3 : (c - b^2 / 4) > 0). { nra. } nra.
Qed.

Lemma lemma_1_18_c : forall x y,
  (x <> 0 \/ y <> 0) -> x^2 + x * y + y^2 > 0.
Proof.
  intros x y [H1 | H1].
  - replace (x^2 + x * y + y^2) with (y^2 + x * y + x^2) by nra. apply lemma_1_18_b. nra.  
  - rewrite Rmult_comm with (r1 := x) (r2 := y). apply lemma_1_18_b. nra.
Qed.

Lemma lemma_1_18_d : forall x y a,
  (x <> 0 \/ y <> 0) -> a^2 < 4 -> x^2 + a * x * y + y^2 > 0.
Proof.
  intros x y a [H1 | H1].
  - intro H2. replace (x^2 + a*x * y + y^2) with (y^2 + a * x * y + x^2) by nra. apply lemma_1_18_b. assert (H3 : x^2 > 0) by nra. nra.
  - intro H2. replace (x^2 + a * x * y + y^2) with ((x + a * y / 2)^2 + (y^2 - a^2 * y^2 / 4)) by nra.
    assert (H3 : (x + a * y / 2)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
    replace (y^2 - a^2 * y^2 / 4) with (y^2 * (1 - a^2 / 4)) by nra. assert (H4 : y^2 > 0) by nra. nra.
Qed.

Lemma lemma_1_18_d' : forall a, a^2 >= 4 -> exists x y, (x <> 0 \/ y <> 0) -> x^2 + a * x * y + y^2 <= 0.
Proof.
  intros a H1. assert (H2 : a <= -2 \/ a >= 2) by nra. destruct H2 as [H2 | H2].
  - exists 1, 1. intros [H3 | H3].
    -- nra.
    -- nra.
  - exists (1), (-1). intros [H3 | H3].
    -- nra.
    -- nra.
Qed.

Lemma lemma_1_18_e : forall x b c,
  c - b^2 / 4 <=  x^2 + b * x + c /\ (x = -b / 2 -> x^2 + b * x + c = c - b^2 / 4).
Proof.
  intros x b c. split.
  - replace (x^2 + b * x + c) with ((x + b / 2)^2 + (c - b^2 / 4)) by nra.
    assert (H1 : (x + b / 2)^2 >= 0). { apply Rle_ge. rewrite <- Rsqr_pow2. apply Rle_0_sqr. }
    nra.
  - intros H1. rewrite H1. nra.
Qed.

Lemma lemma_1_18_e' : forall x a b c,
  a > 0 -> c - b^2 / (4 * a) <= a * x^2 + b * x + c /\ (x = -b / (2 * a) -> a * x^2 + b * x + c = c - b^2 / (4 * a)).
Proof.
  intros x a b c H1. split.
  - replace (a * x^2 + b * x + c) with (a * (x^2 + (b / a) * x + c / a)).
    2 : { replace (a * (x^2 + (b / a) * x + c / a)) with (a * x^2 + a * (b / a * x) + a * (c / a)) by nra. field. nra. }
    assert (H3 : c / a - (b / a)^2 / 4 <= x^2 + (b / a) * x + c / a) by apply lemma_1_18_e.
    apply Rmult_le_compat_r with (r := a) in H3. 2 : { lra. } 
    replace ((c / a - (b / a)^2 / 4) * a) with (c / a * a - ((b / a)^2 / 4) * a) in H3 by nra.
    replace (c / a * a) with c in H3. 2 : { replace (c / a * a) with (a * /a * c) by nra. rewrite Rinv_r. 2 : { lra. } nra. }
    replace ((b / a) ^ 2 / 4 * a) with (b ^ 2 / (4 * a)) in H3 by (field; lra). nra.
  - intro H2. rewrite H2. field; nra.
Qed.