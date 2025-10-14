From Lib Require Import Imports Rational.
From Calculus Require Import Problem_2_13.
Open Scope Z_scope.

Lemma lemma_2_14_a : irrational (sqrt 2 + sqrt 6).
Proof.
  assert (irrational (sqrt 2 + sqrt 6) \/ rational (sqrt 2 + sqrt 6)) as [H1 | H1].
  { unfold irrational. tauto. }
  - auto.
  - assert (sqrt 2 + sqrt 6 <> 0)%R as H2.
    { pose proof sqrt_lt_R0 2 as H2. pose proof sqrt_lt_R0 6 as H3. nra. }
    assert (rational ((sqrt 2 + sqrt 6)^2)) as H3.
    { simpl. rewrite Rmult_1_r. apply mult_rational; auto. }
    replace ((sqrt 2 + sqrt 6)^2)%R with (8 + 4 * sqrt 3)%R in H3.
    2 : 
    { 
      simpl. repeat rewrite Rmult_plus_distr_r. repeat rewrite Rmult_1_r. repeat rewrite Rmult_plus_distr_l.
      repeat rewrite sqrt_sqrt; try lra. repeat rewrite <- sqrt_mult_alt; try lra. rewrite Rmult_comm with (r1 := 2%R).
      replace (sqrt (6 * 2)) with (2 * sqrt 3)%R. 2 : { replace (6 * 2)%R with ((2 * 2) * 3)%R by lra. 
      rewrite sqrt_mult_alt; try lra. rewrite sqrt_square; lra. } lra.
    }
    apply rational_plus_rev with (a := 8%R) (b := (4 * sqrt 3)%R) in H3 as H4.
    2 : { exists 8, 1. lra. }
    apply rational_mult_rev with (a := 4%R) (b := sqrt 3) in H4 as H5.
    2 : { lra. }
    2 : { exists 4, 1. lra. }
    pose proof lemma_2_13_a as H6. unfold irrational in H6. tauto.
Qed.

Lemma lemma_2_14_b : irrational (sqrt 2 + sqrt 3).
Proof.
  assert (irrational (sqrt 2 + sqrt 3) \/ rational (sqrt 2 + sqrt 3)) as [H1 | H1].
  { unfold irrational. tauto. }
  - auto.
  - assert (sqrt 2 + sqrt 3 <> 0)%R as H2.
    { pose proof sqrt_lt_R0 2 as H2. pose proof sqrt_lt_R0 3 as H3. nra. }
    assert (rational ((sqrt 2 + sqrt 3)^2)) as H3.
    { simpl. rewrite Rmult_1_r. apply mult_rational; auto. }
    replace ((sqrt 2 + sqrt 3)^2)%R with (5 + 2 * sqrt 6)%R in H3.
    2 : 
    { 
      simpl. repeat rewrite Rmult_plus_distr_r. repeat rewrite Rmult_1_r. repeat rewrite Rmult_plus_distr_l.
      repeat rewrite sqrt_sqrt; try lra. repeat rewrite <- sqrt_mult_alt; try lra. rewrite Rmult_comm with (r1 := 2%R).
      replace (2 * 3)%R with 6%R by lra. replace (3 * 2)%R with 6%R by lra. nra.
    }
    apply rational_plus_rev with (a := 5%R) (b := (2 * sqrt 6)%R) in H3 as H4.
    2 : { exists 5, 1. lra. }
    apply rational_mult_rev with (a := 2%R) (b := sqrt 6) in H4 as H5.
    2 : { lra. }
    2 : { exists 2, 1. lra. }
    pose proof lemma_2_13_a'' as H6. unfold irrational in H6. tauto.
Qed.