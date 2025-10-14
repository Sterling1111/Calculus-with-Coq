From Lib Require Import Imports Rational.
Open Scope Z_scope.

Lemma lemma_2_12_a : forall a b,
  rational a -> rational b -> rational (a + b).
Proof.
  intros a b [z1 [z2 H1]] [z3 [z4 H2]].
  assert ((a = 0 \/ b = 0 \/ a <> 0 /\ b <> 0)%R) as [H3 | [H3 | H3]] by lra.
  - exists z3. exists z4. nra.
  - exists z1. exists z2. nra.
  - assert (H4 : forall x y z, (x <> 0 /\ x = IZR y / IZR z)%R -> z <> 0).
    { intros x y z [H4 H5]. assert (z <> 0 \/ z = 0) as [H6 | H6] by lia. auto. rewrite H6 in H5. rewrite Rdiv_0_r in H5. nra. }
    assert (H5 : z2 <> 0 /\ z4 <> 0). { split. apply H4 with (x := a) (y := z1). tauto. apply H4 with (x := b) (y := z3). tauto. }
    unfold rational. exists (z1 * z4 + z3 * z2). exists (z2 * z4). rewrite H1. rewrite H2. rewrite plus_IZR.
    repeat rewrite mult_IZR. field; split; apply not_0_IZR; lia.
Qed.

Lemma lemma_2_12_a' : forall a,
  irrational a -> exists b, irrational b /\ rational (a + b).
Proof.
  intros a H1. exists (-a)%R. split.
  - intros [z1 [z2 H2]]. apply H1. exists (-z1), z2. replace (-z1) with (-1 * z1) by lia. rewrite mult_IZR. lra.
  - exists 0, 1. nra.
Qed.

Lemma lemma_2_12_b : forall b,
  irrational b -> exists a, rational a /\ rational (a * b).
Proof.
  intros a H1. exists 0%R. split; exists 0, 1; nra.
Qed.

Lemma lemma_2_12_b' : forall a b,
  a <> 0%R -> rational a -> irrational b -> irrational (a * b).
Proof.
  intros a b H1 H2 H3. assert (irrational (a * b) \/ rational (a * b)) as [H4 | H4].
  { unfold irrational. tauto. } auto.
  destruct H2 as [z1 [z2 H2]]. assert (H5 : z1 <> 0). { apply x_neq_0_IZR_num_neq_0 with (x := a) (y := z1) (z := z2). auto. }
  assert (H6 : z2 <> 0). { apply x_neq_0_IZR_den_neq_0 with (x := a) (y := z1) (z := z2). auto. }
  assert (H7 : rational (/ a)) by (exists z2, z1; rewrite H2; field; split; apply not_0_IZR; lia).
  assert (H8 : b <> 0%R) by (intros H8; apply H3; exists 0, 1; nra).
  assert (H9 : (/ a <> 0)%R) by (apply Rinv_neq_0_compat; auto).
  assert (H10 : rational b).
  { replace b with (a * b / a)%R by (field; auto). apply mult_rational; auto. }
  unfold irrational in H3. tauto.
Qed.

Lemma lemma_2_12_a'' : exists a b, irrational (a + b).
Proof.
  exists (sqrt 2), (sqrt 2). replace (sqrt 2 + sqrt 2)%R with (2 * sqrt 2)%R by lra. apply lemma_2_12_b' with (a := 2%R) (b := (sqrt 2)%R).
  - lra.
  - exists 2, 1. nra.
  - apply sqrt_2_irrational.
Qed.

Lemma lemma_2_12_c : exists a,
  irrational (a^2) /\ rational (a^4).
Proof.
  exists (sqrt (sqrt 2)). split.
  - simpl. rewrite Rmult_1_r. rewrite sqrt_sqrt. 2 : { apply Rlt_le. apply sqrt_lt_R0. lra. } apply sqrt_2_irrational.
  - exists 2, 1. simpl. rewrite Rmult_1_r. rewrite sqrt_sqrt. 2 : { apply Rlt_le. apply sqrt_lt_R0. lra. }
    rewrite <- Rmult_assoc. rewrite sqrt_sqrt. 2 : { apply Rlt_le. apply sqrt_lt_R0. lra. } 
    rewrite sqrt_sqrt; nra.
Qed.

Lemma lemma_2_12_d : exists a b,
  irrational a -> irrational b -> rational (a * b) /\ rational (a + b).
Proof.
  exists (sqrt 2), (-(sqrt 2))%R. intros H1 H2. split.
  - exists (-2), 1. replace (sqrt 2 * - sqrt 2)%R with (- (sqrt 2 * sqrt 2))%R by lra. rewrite sqrt_sqrt; lra.
  - exists 0, 1. lra.
Qed.
