From Calculus.Chapter1 Require Import Prelude.

Lemma lemma_1_11_i : forall x, 
  (x = 11 \/ x = -5) <-> |x - 3| = 8.
Proof.
  solve_R.
Qed.

Lemma lemma_1_11_ii : forall x,
  (-5 < x < 11) <-> |x - 3| < 8.
Proof.
  solve_R.
Qed.

Lemma lemma_1_11_iii : forall x,
  (-6 < x < -2) <-> |x + 4| < 2.
Proof.
  solve_R.
Qed.

Lemma lemma_1_11_iv : forall x,
  (x < 1 \/ x > 2) <-> |x - 1| + |x - 2| > 1.
Proof.
  solve_R.
Qed.

Lemma lemma_1_11_v : forall x, |x - 1| + |x + 1| < 2 -> False.
Proof.
  solve_R.
Qed.

Lemma lemma_1_11_vi : forall x, |x - 1| + |x + 1| < 1 -> False.
Proof.
  solve_R.
Qed.

Lemma lemma_1_11_vii : forall x, 
  (x = 1 \/ x = -1) <-> |x - 1| * |x + 1| = 0.
Proof.
  solve_R.
Qed.

Lemma lemma_1_11_viii : forall x,
 (x = (-1 + √ 21) / 2 \/ x = (-1 - √ 21) / 2) <-> |x - 1| * |x + 2| = 3.
Proof.
  intros x. assert (H1 : x^2 + x - 5 = 0 <-> x = (-1 + √ 21) / 2 \/ x = (-1 - √ 21) / 2).
  {
    split.
    {
    intros H1. replace (x^2 + x - 5) with ((x - (-1 + √ 21) / 2) * (x - (-1 - √ 21) / 2)) in H1. 2 :
       {
         set (r1 := (-1 + √ 21) / 2). set (r2 := (-1 - √ 21) / 2). replace ((x - r1) * (x - r2)) with (x^2 - x * (r2 + r1) + r1 * r2) by lra.
         assert (H2 : r1 + r2 = -1).
        { unfold r1, r2. apply Rmult_eq_reg_r with (r := 2). 2 : { lra. } nra. }
         assert (H3 : r1 * r2 = -5). 
         {
            unfold r1, r2. apply Rmult_eq_reg_r with (r := 4). 2 : { lra. }
            replace (((-1 + √ 21) / 2) * ((-1 - √ 21) / 2) * 4) with ((-1 - √ 21) * (-1 + √ 21)) by nra.
            replace (-5 * 4) with (-20) by lra. replace ((-1 - √ 21) * (-1 + √ 21)) with (1^2 - (√ 21)^2) by lra.
            rewrite pow2_sqrt. lra. lra.
         } nra.
       } nra. 
    }
    {
     intros H1. destruct H1 as [H1 | H1].
     {
       rewrite H1. apply Rplus_eq_reg_r with (r := 5). rewrite Rplus_0_l.
       replace (((-1 + √ 21) / 2) ^ 2 + (-1 + √ 21) / 2 - 5 + 5) with (((-1 + √ 21) / 2) * (((-1 + √ 21) / 2) + 1)) by nra.
       apply Rmult_eq_reg_r with (r := 4). 2 : { lra. } replace ((-1 + sqrt 21) / 2 * ((-1 + sqrt 21) / 2 + 1) * 4) with ((-1 + sqrt 21) * (-1 + sqrt 21 + 2)) by nra.
       replace (5 * 4) with 20 by lra. replace (-1 + √ 21 + 2) with (1 + √ 21) by lra. replace ((-1 + √ 21) * (1 + √ 21)) with (-1 + (√ 21)^2) by nra.
       rewrite pow2_sqrt. lra. lra.
     }
     {
      rewrite H1. apply Rplus_eq_reg_r with (r := 5). rewrite Rplus_0_l.
      replace (((-1 - √ 21) / 2) ^ 2 + (-1 - √ 21) / 2 - 5 + 5) with (((-1 - √ 21) / 2) * (((-1 - √ 21) / 2) + 1)) by nra.
      apply Rmult_eq_reg_r with (r := 4). 2 : { lra. } replace ((-1 - sqrt 21) / 2 * ((-1 - sqrt 21) / 2 + 1) * 4) with ((-1 - sqrt 21) * (-1 - sqrt 21 + 2)) by nra.
      replace (5 * 4) with 20 by lra. replace (-1 - √ 21 + 2) with (1 - √ 21) by lra. replace ((-1 - √ 21) * (1 - √ 21)) with (-1 + (√ 21)^2) by nra.
      rewrite pow2_sqrt. lra. lra.
     }
    } 
  } solve_R. 
Qed.