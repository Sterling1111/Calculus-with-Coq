From Lib Require Import Imports Reals_util.

Open Scope R_scope.

Definition C : Type := R * R.
Definition C0 : C := (0,0).
Definition C1 : C := (1,0).
Definition Ci : C := (0,1).
Definition RtoC (r : R) : C := (r,0).

Coercion RtoC : R >-> C.

Definition Cplus (c1 c2 : C) : C := (fst c1 + fst c2, snd c1 + snd c2).
Definition Copp (c : C) : C := (- fst c, - snd c).
Definition Cminus (c1 c2 : C) : C := Cplus c1 (Copp c2).
Definition Cmult (c1 c2 : C) : C :=
    (fst c1 * fst c2 - snd c1 * snd c2, fst c1 * snd c2 + snd c1 * fst c2).
Definition Cinv (c : C) : C :=
  (fst c / (fst c ^ 2 + snd c ^ 2), - snd c / (fst c ^ 2 + snd c ^ 2)).
Definition Cdiv (c1 c2 : C) : C := Cmult c1 (Cinv c2).
Definition Cnorm2 (c : C) : R := fst c ^ 2 + snd c ^ 2.
Definition Cnorm (c : C) : R := sqrt (Cnorm2 c).

Arguments Cnorm2 c /.
Arguments Cnorm c /.

Declare Scope C_scope.
Delimit Scope C_scope with C.

Notation "| c |" := (Cnorm c) 
  (at level 35, c at level 0, format "| c |", no associativity) : C_scope.

Infix "+" := Cplus : C_scope.
Notation "- x" := (Copp x) : C_scope.
Infix "-" := Cminus : C_scope.
Infix "*" := Cmult : C_scope.
Notation "/ x" := (Cinv x) : C_scope.
Infix "/" := Cdiv : C_scope.


Lemma c_proj_eq : forall (c1 c2 : C),
  fst c1 = fst c2 -> snd c1 = snd c2 -> c1 = c2.
Proof. intros. destruct c1, c2. simpl in *. subst. reflexivity. Qed.

Lemma c_proj_eq_inv : forall (c1 c2 : C),
  c1 = c2 -> fst c1 = fst c2 /\ snd c1 = snd c2.
Proof. intros. inversion H. split; reflexivity. Qed.

Ltac lca := eapply c_proj_eq; simpl; lra.

Open Scope C_scope.

Lemma C1_neq_C0 : C1 <> C0. Proof. intros F. inversion F. lra. Qed.

Lemma Cplus_comm : forall c1 c2 : C, c1 + c2 = c2 + c1. Proof. intros. lca. Qed.

Lemma Cplus_assoc : forall c1 c2 c3 : C, c1 + c2 + c3 = c1 + (c2 + c3).
Proof. intros. lca. Qed.

Lemma Cplus_opp_r : forall c : C, c + - c = 0. Proof. intros. lca. Qed.
Lemma Cplus_0_l :  forall c : C, 0 + c = c. Proof. intros. lca. Qed.
Lemma Cmult_comm : forall c1 c2:C, c1 * c2 = c2 * c1. Proof. intros. lca. Qed.
Lemma Cmult_assoc : forall c1 c2 c3:C, c1 * c2 * c3 = c1 * (c2 * c3).
Proof. intros. lca. Qed.
Lemma Cmult_1_l : forall c:C, 1 * c = c. Proof. intros. lca. Qed.
Lemma Cmult_plus_distr_r : forall c1 c2 c3:C, (c1 + c2) * c3 = c1 * c3 + c2 * c3.
Proof. intros. lca. Qed.

Lemma Cinv_l : forall c:C, c <> 0 -> / c * c = 1.
Proof.
  intros.
  eapply c_proj_eq; simpl; unfold Rminus, Rdiv.
  - repeat rewrite <- Ropp_mult_distr_l.
    rewrite Ropp_involutive.
    repeat rewrite Rmult_1_r.
    rewrite (Rmult_comm (fst c)). rewrite Rmult_assoc.
    rewrite (Rmult_comm (snd c) (/ _)). rewrite Rmult_assoc.
    rewrite <- Rmult_plus_distr_l.
    rewrite Rinv_l; try lra.
    contradict H. apply Rplus_sqr_eq_0 in H. lca.
  - repeat rewrite Rmult_1_r.
    rewrite (Rmult_comm (fst c)). rewrite Rmult_assoc.
    rewrite (Rmult_comm (- snd c)). rewrite Rmult_assoc.
    rewrite <- Rmult_plus_distr_l.
    lra.
Qed.

Lemma C_Field_Theory : @field_theory C 0 1 Cplus Cmult Cminus Copp Cdiv Cinv eq.
Proof.
  constructor. constructor.
  (* addition *)
  (* left identity *) apply Cplus_0_l.
  (* commutativity *) apply Cplus_comm.
  (* associativity *) intros; rewrite Cplus_assoc; easy.
  (* multiplication *)
  (* left identity *) apply Cmult_1_l.
  (* commutativity *) apply Cmult_comm.
  (* associativity *) intros; rewrite Cmult_assoc; easy.
  (* distributivity *) apply Cmult_plus_distr_r.
  (* sub = opp *) reflexivity.
  (* additive inverse *) apply Cplus_opp_r.
  (* 0 <> 1 *) apply C1_neq_C0.
  (* div = inv *) reflexivity.
  (* multiplicative inverse *) apply Cinv_l.
Defined.

Add Field CField : C_Field_Theory.

Lemma Cplus_opp_l : forall c : C, - c + c = 0. Proof. intros. lca. Qed.
Lemma Cplus_0_r : forall c : C, c + 0 = c. Proof. intros. lca. Qed.
Lemma Cmult_0_l : forall c:C, 0 * c = 0. Proof. intros. lca. Qed.
Lemma Cmult_0_r : forall c:C, c * 0 = 0. Proof. intros. lca. Qed.
Lemma Cmult_1_r : forall c:C, c * 1 = c. Proof. intros. lca. Qed.
Lemma Cmult_plus_distr_l : forall c1 c2 c3:C, c1 * (c2 + c3) = c1 * c2 + c1 * c3.
Proof. intros. lca. Qed.
Lemma Cinv_r : forall c:C, c <> 0 -> c * /c = 1.
Proof. intros. rewrite Cmult_comm. apply Cinv_l. easy. Qed.
Lemma Copp_mult_distr_r : forall c1 c2 : C, - (c1 * c2) = c1 * - c2.
Proof. intros; lca. Qed.
Lemma Copp_mult_distr_l : forall c1 c2 : C, - (c1 * c2) = - c1 * c2.
Proof. intros; lca. Qed.
Lemma Copp_involutive: forall c : C, - - c = c. Proof. intros; lca. Qed.

Lemma Csqrt2_square : sqrt 2 * sqrt 2 = 2.
Proof.
  eapply c_proj_eq; simpl; try lra.
  rewrite Rmult_0_r, Rminus_0_r.
  apply sqrt_def.
  lra.
Qed.

Lemma RtoC_neq : forall (r1 r2 : R), r1 <> r2 -> RtoC r1 <> RtoC r2.
Proof. intros r1 r2 H F. inversion F. easy. Qed.

Definition Cconj (x : C) : C := (fst x, (- snd x)%R).
Notation "a ^*" := (Cconj a) (at level 10) : C_scope.
Lemma Cconj_R : forall r : R, r^* = r. Proof. intros; lca. Qed.
Lemma Cconj_0 : 0^* = 0. Proof. lca. Qed.
Lemma Cconj_opp : forall C, (- C)^* = - (C^*). Proof. reflexivity. Qed.
Lemma Cconj_rad2 : (/ (sqrt 2))^* = / (sqrt 2). Proof. lca. Qed.
Lemma Cconj_involutive : forall c, (c^*)^* = c. Proof. intros; lca. Qed.
Lemma Cconj_plus_distr : forall (x y : C), (x + y)^* = x^* + y^*. Proof. intros; lca. Qed.
Lemma Cconj_mult_distr : forall (x y : C), (x * y)^* = x^* * y^*. Proof. intros; lca. Qed.

Definition Csqr c : C := c * c.
Notation "c ²" := (Csqr c) (at level 1, format "c ²") : C_scope.

Fixpoint Cpow (c : C) (n : nat) : C :=
  match n with
  | 0%nat => 1
  | S n' => c * Cpow c n'
  end.

Infix "^" := Cpow : C_scope.

Lemma Csqr_pow2 : forall x, Csqr x = x ^ 2.
  Proof. intros. unfold Cpow. unfold Csqr. rewrite Cmult_1_r. reflexivity.
Qed.

Open Scope R_scope.

Ltac solve_C :=
  intros;
  repeat match goal with
  | c : C |- _ => destruct c
  end;
  simpl in *;
  try (unfold Cnorm, Cnorm2, Cplus, Cminus, Copp, Cmult in *);
  try field_simplify_eq;
  solve_R.

Lemma Cnorm_fst : forall c : C, Rabs (fst c) <= Cnorm c.
Proof.
  intros [x y]. unfold Cnorm, Cnorm2; simpl.
  replace (Rabs x) with (sqrt (x^2)).
  - apply sqrt_le_1_alt. 
    assert (H_yx : x * (x * 1) + y * (y * 1) = x^2 + y^2) by (simpl; lra).
    rewrite H_yx.
    assert (0 <= y^2) by (apply pow2_ge_0; lra). lra.
  - assert (H_x2 : x^2 = x * x) by (simpl; lra).
    rewrite H_x2. rewrite <- Rsqr_def. apply sqrt_Rsqr_abs.
Qed.

Lemma Cnorm_snd : forall c : C, Rabs (snd c) <= Cnorm c.
Proof.
  intros [x y]. unfold Cnorm, Cnorm2; simpl.
  replace (Rabs y) with (sqrt (y^2)).
  - apply sqrt_le_1_alt. 
    assert (H_yx : x * (x * 1) + y * (y * 1) = x^2 + y^2) by (simpl; lra).
    rewrite H_yx.
    assert (0 <= x^2) by (apply pow2_ge_0; lra). lra.
  - assert (H_y2 : y^2 = y * y) by (simpl; lra).
    rewrite H_y2. rewrite <- Rsqr_def. apply sqrt_Rsqr_abs.
Qed.

Lemma Cnorm_le_sum_abs : forall c : C, Cnorm c <= Rabs (fst c) + Rabs (snd c).
Proof.
  intros [x y]. unfold Cnorm, Cnorm2; simpl.
  assert (H_yx : x * (x * 1) + y * (y * 1) = x^2 + y^2) by (simpl; lra).
  rewrite H_yx.
  replace (Rabs x + Rabs y) with (sqrt ((Rabs x + Rabs y)^2)).
  - apply sqrt_le_1_alt.
    assert (H_sq : (Rabs x + Rabs y)^2 = Rabs x ^ 2 + Rabs y ^ 2 + 2 * Rabs x * Rabs y) by (simpl; lra).
    rewrite H_sq.
    assert (Rabs x ^ 2 = x^2).
    { assert (H_1 : Rabs x ^ 2 = Rabs x * Rabs x) by (simpl; lra).
      rewrite H_1. rewrite <- Rsqr_def, <- Rsqr_abs, Rsqr_def. simpl; lra. }
    assert (Rabs y ^ 2 = y^2).
    { assert (H_2 : Rabs y ^ 2 = Rabs y * Rabs y) by (simpl; lra).
      rewrite H_2. rewrite <- Rsqr_def, <- Rsqr_abs, Rsqr_def. simpl; lra. }
    assert (0 <= 2 * Rabs x * Rabs y).
    { apply Rmult_le_pos. apply Rmult_le_pos; [lra | apply Rabs_pos]. apply Rabs_pos. }
    lra.
  - assert (H_3 : (Rabs x + Rabs y)^2 = (Rabs x + Rabs y) * (Rabs x + Rabs y)) by (simpl; lra).
    rewrite H_3. rewrite <- Rsqr_def. apply sqrt_Rsqr.
    assert (0 <= Rabs x) by apply Rabs_pos.
    assert (0 <= Rabs y) by apply Rabs_pos.
    lra.
Qed.

Open Scope C_scope.

Lemma Cconj_real : forall c,
  c^* = c <-> snd c = 0.
Proof.
  intros c. split; intros H1.
  - apply c_proj_eq_inv in H1 as [H2 H3]. simpl in H3. lra.
  - destruct c; simpl in *. subst. lca.
Qed.

Lemma Cconj_inv : forall c,
  (/ c)^* = / (c^*).
Proof.
  intros c. apply c_proj_eq; simpl.
  - f_equal. f_equal. ring.
  - unfold Rdiv. replace (fst c * (fst c * 1) + snd c * (snd c * 1))%R with (fst c * (fst c * 1) + - snd c * (- snd c * 1))%R by ring. lra.
Qed.

Lemma Cmult_conj_Cnorm2 : forall c,
  c * c^* = RtoC (Cnorm2 c).
Proof.
  intros c. lca.
Qed.

Lemma Cnorm_ge_0 : forall c : C,
  (Cnorm c >= 0)%R.
Proof.
  intros c. unfold Cnorm. apply Rle_ge. apply sqrt_pos.
Qed.

Lemma Cnorm_eq_0 : forall c : C,
  (Cnorm c = 0)%R <-> c = 0.
Proof.
  intros [x y]. split; intros H1.
  - unfold Cnorm, Cnorm2 in H1. simpl in H1.
    apply sqrt_eq_0 in H1.
    + assert (H2 : (x^2)%R = 0 /\ (y^2)%R = 0).
      { assert (H_x : (0 <= x^2)%R) by apply pow2_ge_0.
        assert (H_y : (0 <= y^2)%R) by apply pow2_ge_0. lra. }
      destruct H2 as [H2 H3]. apply c_proj_eq; simpl; nra.
    + assert (H2 : (0 <= x^2)%R) by apply pow2_ge_0.
      assert (H3 : (0 <= y^2)%R) by apply pow2_ge_0. lra.
  - inversion H1. unfold Cnorm, Cnorm2. simpl.
    replace (0 * (0 * 1) + 0 * (0 * 1))%R with 0%R by lra. apply sqrt_0.
Qed.

Lemma Cnorm_mult : forall c1 c2 : C,
  Cnorm (c1 * c2) = (Cnorm c1 * Cnorm c2)%R.
Proof.
  intros [x1 y1] [x2 y2]. unfold Cnorm, Cnorm2, Cmult. simpl.
  rewrite <- sqrt_mult.
  - apply f_equal. ring.
  - assert (H1 : (0 <= x1^2)%R) by apply pow2_ge_0.
    assert (H2 : (0 <= y1^2)%R) by apply pow2_ge_0. lra.
  - assert (H1 : (0 <= x2^2)%R) by apply pow2_ge_0.
    assert (H2 : (0 <= y2^2)%R) by apply pow2_ge_0. lra.
Qed.

Lemma Cnorm_triangle : forall c1 c2 : C,
  (Cnorm (c1 + c2)%C <= Cnorm c1 + Cnorm c2)%R.
Proof.
  intros [x1 y1] [x2 y2]. unfold Cnorm, Cnorm2, Cplus; simpl.
  apply Rsqr_incr_0.
  - repeat rewrite Rsqr_sqrt.
    + replace ((x1 + x2) * ((x1 + x2) * 1) + (y1 + y2) * ((y1 + y2) * 1))%R with
        (x1 * (x1 * 1) + y1 * (y1 * 1) + x2 * (x2 * 1) + y2 * (y2 * 1) + 2 * (x1 * x2 + y1 * y2))%R by ring.
      unfold Rsqr.
      replace ((sqrt (x1 * (x1 * 1) + y1 * (y1 * 1)) + sqrt (x2 * (x2 * 1) + y2 * (y2 * 1))) * (sqrt (x1 * (x1 * 1) + y1 * (y1 * 1)) + sqrt (x2 * (x2 * 1) + y2 * (y2 * 1))))%R with
        (x1 * (x1 * 1) + y1 * (y1 * 1) + x2 * (x2 * 1) + y2 * (y2 * 1) + 2 * (sqrt (x1 * (x1 * 1) + y1 * (y1 * 1)) * sqrt (x2 * (x2 * 1) + y2 * (y2 * 1))))%R.
      * apply Rplus_le_compat_l.
        apply Rmult_le_compat_l; [lra |].
        rewrite <- sqrt_mult.
        -- apply Rle_trans with (r2 := Rabs (x1 * x2 + y1 * y2)).
           { apply Rle_abs. }
           rewrite <- sqrt_Rsqr_abs.
           replace (Rsqr (x1 * x2 + y1 * y2))%R with ((x1 * x2 + y1 * y2) * ((x1 * x2 + y1 * y2) * 1))%R by (unfold Rsqr; ring).
           apply sqrt_le_1_alt.
           replace ((x1 * (x1 * 1) + y1 * (y1 * 1)) * (x2 * (x2 * 1) + y2 * (y2 * 1)))%R with
             ((x1 * x2 + y1 * y2) * ((x1 * x2 + y1 * y2) * 1) + (x1 * y2 - x2 * y1) * ((x1 * y2 - x2 * y1) * 1))%R by ring.
           assert (H1 : (0 <= (x1 * y2 - x2 * y1) * ((x1 * y2 - x2 * y1) * 1))%R) by apply pow2_ge_0. lra.
        -- assert (H1 : (0 <= x1 * (x1 * 1))%R) by apply pow2_ge_0.
           assert (H2 : (0 <= y1 * (y1 * 1))%R) by apply pow2_ge_0. lra.
        -- assert (H1 : (0 <= x2 * (x2 * 1))%R) by apply pow2_ge_0.
           assert (H2 : (0 <= y2 * (y2 * 1))%R) by apply pow2_ge_0. lra.
      * rewrite Rmult_plus_distr_l, Rmult_plus_distr_r, Rmult_plus_distr_r.
        repeat rewrite sqrt_sqrt; try (assert (H1 : (0 <= x1 * (x1 * 1))%R) by apply pow2_ge_0; assert (H2 : (0 <= y1 * (y1 * 1))%R) by apply pow2_ge_0; lra).
        try (assert (H1 : (0 <= x2 * (x2 * 1))%R) by apply pow2_ge_0; assert (H2 : (0 <= y2 * (y2 * 1))%R) by apply pow2_ge_0; lra).
    + assert (H1 : (0 <= (x1 + x2) * ((x1 + x2) * 1))%R) by apply pow2_ge_0.
      assert (H2 : (0 <= (y1 + y2) * ((y1 + y2) * 1))%R) by apply pow2_ge_0. lra.
  - apply sqrt_pos.
  - apply Rplus_le_le_0_compat; apply sqrt_pos.
Qed.