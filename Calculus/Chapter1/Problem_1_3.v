From Calculus.Chapter1 Require Import Prelude.

(*we dont need b <> 0 in this proof because in coq r / 0 = 0 so it hold true anyway*)
Lemma lemma_1_3_i : forall a b c : R,
  b <> 0 /\ c <> 0 -> a / b = (a * c) / (b * c).
Proof.
  intros a b c [H1 H2].
  unfold Rdiv.
  rewrite Rinv_mult. rewrite Rmult_assoc. rewrite Rmult_comm with (r1 := c).
  rewrite Rmult_assoc with (r3 := c). rewrite Rinv_l. 2 : { apply H2. }
  rewrite Rmult_1_r. reflexivity.
Qed.

Lemma lemma_1_3_ii : forall a b c d : R,
  b <> 0 /\ d <> 0 -> a / b + c / d = (a * d + b * c) / (b * d).
Proof.
  intros a b c d [H1 H2].
  unfold Rdiv. rewrite Rinv_mult. rewrite <- Rmult_assoc. 
  apply Rmult_eq_reg_r with (r := d). 2 : { apply H2. }
  rewrite Rmult_plus_distr_r. rewrite Rmult_assoc with (r1 := c).
  rewrite Rinv_l. 2 : { apply H2. } rewrite Rmult_1_r. 
  rewrite Rmult_plus_distr_r. rewrite Rmult_comm with (r1 := b).
  rewrite Rmult_assoc with (r1 := c). rewrite Rinv_r. 2 : { apply H1. }
  rewrite Rmult_1_r. rewrite Rmult_assoc with (r2 := /d). rewrite Rinv_l.
  2 : { apply H2. } rewrite Rmult_1_r. rewrite Rmult_assoc. rewrite Rmult_comm with (r2 := d).
  rewrite Rmult_assoc. reflexivity.
Qed.

Definition Zpow (b : R) (e : Z) : R :=
  if Z.ltb e 0 then 1 / (b ^ Z.to_nat (Z.abs e)) else b ^ Z.to_nat e.

Lemma lemma_1_3_iii : forall a b : R,
  a > 0 /\ b > 0 -> Rpower (a * b) (-1) = Rpower a (-1) * Rpower b (-1).
Proof.
  intros a b [H1 H2].
  repeat rewrite Rpower_Ropp with (y := 1). repeat rewrite Rpower_1.
  2 : {  apply H2. } 2 : { apply H1. } 2 : { apply Rmult_lt_0_compat; assumption. }
  apply Rinv_mult.
Qed.

Lemma lemma_1_3_iii' : forall a b : R, 
  a <> 0 /\ b <> 0 -> Zpow (a * b) (-1)%Z = Zpow a (-1)%Z * Zpow b (-1)%Z.
Proof.
  intros a b [H1 H2].
  - unfold Zpow. simpl. field; lra.
Qed.

Lemma lemma_1_3_iv : forall a b c d : R,
  b <> 0 /\ d <> 0 -> (a / b) * (c / d) = (a * c) / (d * b).
Proof.
  intros a b c d [H1 H2].
  unfold Rdiv. rewrite Rinv_mult.
  rewrite Rmult_assoc. rewrite Rmult_assoc. rewrite Rmult_comm with (r2 := /d * /b).
  rewrite Rmult_comm with (r1 := /d). rewrite Rmult_assoc with (r1 := /b).
  rewrite Rmult_comm with (r1 := /d). reflexivity.
Qed.

Lemma lemma_1_3_v : forall a b c d : R,
  b <> 0 /\ c <> 0 /\ d <> 0 -> (a / b) / (c / d) = (a * d) / (b * c).
Proof.
  intros a b c d [H1 [H3 H4]].
  unfold Rdiv. repeat rewrite Rinv_mult. rewrite Rinv_inv. lra. (*more tedius assoc + commutativity who cares*) 
Qed.

Lemma lemma_1_3_vi : forall a b c d, 
  b <> 0 /\ d <> 0 -> a / b = c / d <-> a * d = b * c.
Proof.
  intros a b c d [H1 H2].
  split.
  - intros H3. apply Rmult_eq_compat_r with (r := b) in H3.
    unfold Rdiv in H3. rewrite Rmult_assoc in H3.
    rewrite Rinv_l in H3. 2 : { apply H1. } rewrite Rmult_1_r in H3.
    rewrite -> H3. replace (c * / d * b * d) with (/d * d * b * c) by lra.
    rewrite Rinv_l. 2 : { apply H2. } rewrite Rmult_1_l. reflexivity.
  - intros H3. apply Rmult_eq_compat_r with (r := /d) in H3.
    unfold Rdiv in H3. rewrite Rmult_assoc in H3. rewrite Rinv_r in H3. 2 : { apply H2. }
    rewrite Rmult_1_r in H3. rewrite H3. unfold Rdiv.
    replace (b * c * /d * /b) with (c * /d *( b * /b)) by lra. rewrite Rinv_r.
    2 : {apply H1. } rewrite Rmult_1_r. reflexivity.
Qed.