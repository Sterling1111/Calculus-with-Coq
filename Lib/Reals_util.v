From Lib Require Import Imports.

Open Scope R_scope.

Coercion INR : nat >-> R.
Coercion IZR : Z >-> R.

Ltac break_INR :=
  repeat match goal with
  | [ |- context[INR (?n + ?m)] ] =>
      rewrite plus_INR
  | [ |- context[INR (?n * ?m)] ] =>
      rewrite mult_INR
  | [ |- context[INR (S ?n)] ] =>
      rewrite S_INR
  | [ |- context[INR (?n - ?m)] ] =>
      rewrite minus_INR
  | [ |- context[INR (?n ^ ?m)] ] =>
      rewrite pow_INR
  end.

Ltac convert_nat_to_INR_in_H :=
  try
  match goal with
  | [ H: (?x > ?y)%nat |- _ ] => apply lt_INR in H; simpl in H
  | [ H: (?x < ?y)%nat |- _ ] => apply lt_INR in H; simpl in H
  | [ H: (?x >= ?y)%nat |- _ ] => apply le_INR in H; simpl in H
  | [ H: (?x <= ?y)%nat |- _ ] => apply le_INR in H; simpl in H
  | [ H: (?x = ?y)%nat |- _ ] => apply INR_eq in H; simpl in H
  end.

Ltac break_INR_simpl :=
  break_INR; simpl; try field_simplify; try lra; try nra; try nia.

Ltac solve_INR :=
  convert_nat_to_INR_in_H; try field_simplify_eq; try break_INR; simpl; try field; try lra; try nra; try lia.

Ltac solve_abs := 
  try intros; 
  try lra; 
  unfold Rabs in *; 
  repeat match goal with
  | [ |- context[if Rcase_abs ?x then _ else _] ] => 
      destruct (Rcase_abs x); try lra
  | [ H: context[if Rcase_abs ?x then _ else _] |- _ ] => 
      destruct (Rcase_abs x); try lra
  | [ Z := context[if Rcase_abs ?x then _ else _] |- _ ] =>
      destruct (Rcase_abs x); try lra
  end;
  try field; try nra; try nia.

Ltac solve_max := 
  try intros; 
  try lra;
  unfold Rmax, Nat.max in *;
  repeat match goal with
  | [ |- context[if Rle_dec ?x ?y then _ else _] ] => 
      destruct (Rle_dec x y); try lra
  | [ H: context[if Rle_dec ?x ?y then _ else _] |- _ ] => 
      destruct (Rle_dec x y); try lra
  | [ |- context[if le_dec ?x ?y then _ else _] ] =>
      destruct (le_dec x y); try lia
  | [ Z := context[if Rle_dec ?x ?y then _ else _] |- _ ] =>
      destruct (Rle_dec x y); try lra
  | [ Z := context[if le_dec ?x ?y then _ else _] |- _ ] =>
      destruct (le_dec x y); try lia
  end;
  try field; try nra; try nia.

Ltac solve_min :=
  try intros; 
  try lra;
  unfold Rmin, Nat.min in *;
  repeat match goal with
  | [ |- context[if Rle_dec ?x ?y then _ else _] ] => 
      destruct (Rle_dec x y); try lra
  | [ H: context[if Rle_dec ?x ?y then _ else _] |- _ ] => 
      destruct (Rle_dec x y); try lra
  | [ |- context[if le_dec ?x ?y then _ else _] ] =>
      destruct (le_dec x y); try lia
  | [ Z := context[if Rle_dec ?x ?y then _ else _] |- _ ] =>
      destruct (Rle_dec x y); try lra
  | [ Z := context[if le_dec ?x ?y then _ else _] |- _ ] =>
      destruct (le_dec x y); try lia
  end;
  try field; try nra; try nia.

Ltac solve_R :=
  unfold Ensembles.In in *; 
  try solve_INR; 
  try solve_abs; 
  try solve_max; 
  try solve_min; 
  try lra; 
  try tauto; 
  auto.

Lemma pow2_gt_0 : forall r, r <> 0 -> r ^ 2 > 0.
Proof.
  intros r H1. pose proof Rtotal_order r 0 as [H2 | [H2 | H2]]; try nra.
Qed.

Lemma Rmult_le_ge_reg_neg_l :
  forall r r1 r2, r * r1 >= r * r2 -> r < 0 -> r1 <= r2.
Proof. intros; nra. Qed.

Lemma Rmult_ge_le_reg_neg_l :
  forall r r1 r2, r * r1 <= r * r2 -> r < 0 -> r1 >= r2.
Proof. intros; nra. Qed.

Lemma Rabs_triang_3 : forall r1 r2 r3 : R,
  Rabs (r1 + r2 + r3) <= Rabs r1 + Rabs r2 + Rabs r3.
Proof.
  solve_abs.
Qed.

Lemma n_lt_pow2_n : forall n, INR n < 2 ^ n.
Proof.
  induction n as [| k IH].
  - simpl. lra.
  - solve_INR. assert (1 <= 2 ^ k).
    { clear; induction k; simpl; lra. } solve_INR.
Qed.

Lemma Rpow_gt_0 : forall k r,
  r > 0 -> r ^ k > 0.
Proof.
  intros k r H1. induction k as [| k' IH].
  - simpl. lra.
  - simpl. nra.
Qed.

Lemma Rpow_lt_1 : forall r n,
  0 < r < 1 -> (n > 0)%nat -> r ^ n < 1.
Proof.
  intros r n [H1 H2] H3. induction n as [| k IH].
  - lia.
  - simpl. destruct k.
    -- simpl. lra.
    -- assert (r ^ S k < 1) by (apply IH; lia). nra.
Qed.

Lemma Rpow_gt_1 : forall r n,
  r > 1 -> (n > 0)%nat -> r ^ n > 1.
Proof.
  intros r n H1 H2. induction n as [| k IH].
  - lia.
  - simpl. destruct k.
    -- simpl. lra.
    -- assert (r ^ S k > 1) by (apply IH; lia). nra.
Qed.

Lemma Rpow_even_gt_0 : forall r n,
  r <> 0 -> (Nat.Even n) -> r ^ n > 0.
Proof.
  intros r n H1 [k H2].
  rewrite H2. rewrite pow_mult. apply Rpow_gt_0. apply pow2_gt_0. auto.
Qed.

Lemma Rpow_odd_lt_0 : forall r n,
  r < 0 -> (Nat.Odd n) -> r ^ n < 0.
Proof.
  intros r n H1 [k H2].
  rewrite H2. rewrite pow_add, pow_mult. rewrite pow_1. 
  assert (H3 : r^2 > 0). { apply pow2_gt_0; lra. }
  assert (H4 : (r^2)^k > 0). { apply Rpow_gt_0; auto. } nra.
Qed.

Lemma Rdiv_pow_distr : forall r1 r2 n,
  r2 > 0 -> (r1 / r2) ^ n = r1 ^ n / r2 ^ n.
Proof.
  intros r1 r2 n H1. induction n as [| k IH].
  - simpl. lra.
  - simpl. rewrite IH. field. pose proof Rpow_gt_0 k r2 as H2; nra.
Qed.

Lemma Rdiv_lt_1: forall a b : R, a < b -> b > 0 -> a / b < 1.
Proof.
  intros a b H1 H2.
  apply Rmult_lt_compat_r with (r := 1/b) in H1.
  - replace (a * (1 / b)) with (a / b) in H1 by lra.
    replace (b * (1 / b)) with 1 in H1 by (field; lra).
    apply H1.
  - apply Rdiv_pos_pos. lra. apply H2.
Qed.  

Lemma pow_incrst_1 : forall r1 r2 n,
  (n > 0)%nat -> r1 >= 0 -> r2 > 0 -> r1 < r2 -> r1^n < r2^n.
Proof.
  intros r1 r2 n H1 H2 H3 H4. generalize dependent r1. generalize dependent r2. induction n as [| k IH].
  - lia.
  - intros r2 H2 r1 H3 H4. simpl. destruct k; try nra. assert (H6 : r1^(S k) < r2 ^(S k)). { apply IH; try lia; try nra. }
    apply Rmult_ge_0_gt_0_lt_compat; try nra. simpl. assert (0 <= r1 ^ k). { apply pow_le; nra. } nra. 
Qed.

Lemma Rlt_pow_base : forall a b n,
  0 <= a -> 0 < b -> (n > 0)%nat -> a^n < b^n -> a < b.
Proof.
  intros a b n H1 H2 H3 H4. induction n as [| k IH].
  - lia.
  - simpl in H4. destruct k.
    -- simpl in H4. lra.
    -- apply IH. lia. simpl. simpl in H4. pose proof Rtotal_order a b as [H5 | [H6 | H7]].
      --- assert (k = 0 \/ k > 0)%nat as [H8 | H8] by lia; subst; try lra.
          assert (H6 : a^k < b^k). { apply pow_incrst_1; try lia; try lra. } assert (H7 : 0 <= a^k). { apply pow_le. lra. } nra.
      --- subst; lra.
      --- assert (k = 0 \/ k > 0)%nat as [H8 | H8] by lia. { rewrite H8 in H4. nra. }
          assert (H9 : b^k < a^k). { apply pow_incrst_1; try lia; try lra. } assert (H10 : b^k > 0). { apply pow_lt. lra. }
          assert (H11 : a * a^k > b * b^k). { nra. } assert (H12 : a * (a * a^k) > b * (b * b^k)). { apply Rmult_gt_0_lt_compat. nra. nra. nra. nra. } nra.
Qed.

Lemma sqrt_2_gt_1 : (1 < sqrt 2)%R.
Proof.
    apply Rlt_pow_base with (n := 2%nat); try lra; try lia. apply sqrt_lt_R0; lra. rewrite pow2_sqrt; lra.
Qed.

Lemma Rinv_lt_contravar_3 : forall a b c,
  a > 0 -> b > 0 -> c > 0 -> a < b < c -> 1 / c < 1 / b < 1 / a.
Proof.
  intros a b c H1 H2 H3 [H4 H5]. split; repeat rewrite Rdiv_1_l; apply Rinv_lt_contravar; nra.
Qed.

Lemma nat_pos_Rpos_iff : ∀ n : nat,
  n > 0 <-> (n > 0)%nat.
Proof.
  intros n; split; intros H1; solve_R.
  apply INR_lt. solve_R.
Qed.

Lemma nat_gt_Rgt_iff : ∀ n m : nat,
  INR n > INR m <-> (n > INR m).
Proof.
  intros n m. solve_R.
Qed.

Ltac compare_elems e1 e2 := 
  let e1' := eval simpl in e1 in
  let e2' := eval simpl in e2 in 
  field_simplify; try nra; try nia.

(* Compare two lists recursively element by element *)
Ltac compare_lists_step :=
  match goal with
  | [ |- [] = [] ] => reflexivity
  | [ |- (?x :: ?xs) = (?y :: ?ys) ] => 
      first [
        assert (x = y) by compare_elems x y;
        apply f_equal2; [assumption | compare_lists_step]
        |
        fail "Elements" x "and" y "cannot be proven equal"
      ]
  | [ |- ?l1 = ?l2 ] =>
      fail "Lists" l1 "and" l2 "have different lengths or structures"
  end.

Ltac auto_list :=
  intros; compute;
  try solve [reflexivity];
  compare_lists_step.

Definition is_natural (r : R) : Prop :=
    exists n : nat, r = INR n.

Definition is_integer (r : R) : Prop :=
    exists z : Z, r = IZR z.

Lemma is_natural_plus : forall r1 r2 : R,
  is_natural r1 -> is_natural r2 -> is_natural (r1 + r2).
Proof.
  intros r1 r2 H1 H2. destruct H1 as [n1 H1]. destruct H2 as [n2 H2]. exists (n1 + n2)%nat. rewrite H1, H2. rewrite plus_INR. reflexivity.
Qed.

Lemma is_natural_mult : forall r1 r2 : R,
  is_natural r1 -> is_natural r2 -> is_natural (r1 * r2).
Proof.
  intros r1 r2 H1 H2. destruct H1 as [n1 H1]. destruct H2 as [n2 H2]. exists (n1 * n2)%nat. rewrite H1, H2. rewrite mult_INR. reflexivity.
Qed. 

Lemma is_integer_plus : forall r1 r2 : R,
  is_integer r1 -> is_integer r2 -> is_integer (r1 + r2).
Proof.
  intros r1 r2 H1 H2. destruct H1 as [z1 H1]. destruct H2 as [z2 H2]. exists (z1 + z2)%Z. rewrite H1, H2. rewrite plus_IZR. reflexivity.
Qed.

Lemma is_integer_mult : forall r1 r2 : R,
  is_integer r1 -> is_integer r2 -> is_integer (r1 * r2).
Proof.
  intros r1 r2 H1 H2. destruct H1 as [z1 H1]. destruct H2 as [z2 H2]. exists (z1 * z2)%Z. rewrite H1, H2. rewrite mult_IZR. reflexivity.
Qed.

Lemma is_integer_pow : forall r n,
  is_integer r -> is_integer (r ^ n).
Proof.
  intros r n H1. induction n as [| k IH].
  - simpl. exists 1%Z. reflexivity.
  - simpl. apply is_integer_mult; try apply IH; auto.
Qed.

Lemma pow_div_sub : forall x n1 n2,
  x <> 0 -> (n2 >= n1)%nat -> x ^ (n2 - n1)%nat = x ^ n2 / x ^ n1.
Proof.
  intros x n1 n2 H1 H3. generalize dependent n1. induction n2 as [| k IH].
  - intros n1 H2. replace (n1) with 0%nat by lia. simpl. lra.
  - intros n1 H2. destruct (Nat.eq_dec n1 (S k)).
    + subst. simpl. rewrite Nat.sub_diag. field. split; auto. apply pow_nonzero; auto.
    + assert (H3 : (n1 <= k)%nat) by lia. replace (S k - n1)%nat with (S (k - n1)) by lia.
      simpl. rewrite IH; auto. field; apply pow_nonzero; auto.
Qed.

Lemma nltb_gt : forall a b : nat, (a > b)%nat <-> (a <=? b) = false.
Proof.
  intros a b. split.
  - intros H1. apply leb_correct_conv; lia.
  - intros H1. destruct (Nat.leb_spec a b); try lia. 
Qed.

Lemma nltb_ge : forall a b : nat, (a >= b)%nat <-> (a <? b) = false.
Proof.
  intros a b. split.
  - intros H1. apply leb_correct_conv; lia.
  - intros H1. destruct (Nat.ltb_spec a b); try lia.
Qed.

Lemma Rmult_gt_reg_neg_r : forall r r1 r2,
  r < 0 -> r1 * r > r2 * r -> r1 < r2.
Proof.
  intros. nra.
Qed.

Lemma cross_multiply_lt : forall r1 r2 r3 r4,
  r1 > 0 -> r2 > 0 -> r3 > 0 -> r4 > 0 ->
  r1 * r4 < r2 * r3 -> r1 / r2 < r3 / r4.
Proof.
  intros r1 r2 r3 r4 H1 H2 H3 H4 H5. apply Rmult_lt_reg_r with (r := r2); 
  apply Rmult_lt_reg_r with (r := r4); field_simplify; nra.
Qed.

Lemma gte_1_INR : forall n : nat,
  0 < n -> 1 <= n.
Proof.
  intros n H1. assert ((INR n = 1) \/ (INR n > 1)) as [H2 | H2]; try lra.
  {
    replace 0 with (INR 0) in * by auto. replace 1 with (INR 1) in * by auto. destruct n.
    - apply INR_lt in H1; lia.
    - apply INR_lt in H1. destruct n; [left; reflexivity | right; apply lt_INR; lia ].
  }
Qed.

Lemma Rdiv_neg_neg_eq : forall r1 r2,
  -r1 / -r2 = r1 / r2.
Proof.
  intros r1 r2. destruct (Req_dec_T r1 0) as [H1 | H1]; destruct (Req_dec_T r2 0) as [H2 | H2]; try nra.
  - rewrite H2, Ropp_0, Rdiv_0_r, Rdiv_0_r. reflexivity.
  - field; auto.
Qed.

Lemma Rdiv_neq_0 : forall r1 r2,
  r2 <> 0 -> r1 / r2 <> 0 <-> r1 <> 0.
Proof.
  intros r1 r2 H1. split; intros H2.
  - intros H3. rewrite H3 in H2. lra.
  - intros H3. pose proof Rtotal_order r1 0 as [H4 | [H4 | H4]]; pose proof Rtotal_order r2 0 as [H5 | [H5 | H5]]; try nra.
    + pose proof Rdiv_neg_neg r1 r2 ltac:(lra) ltac:(lra). nra.
    + pose proof Rdiv_neg_pos r1 r2 ltac:(lra) ltac:(lra). nra.
    + pose proof Rdiv_pos_neg r1 r2 ltac:(lra) ltac:(lra). nra.
    + pose proof Rdiv_pos_pos r1 r2 ltac:(lra) ltac:(lra). nra.
Qed.

Lemma Rdiv_pos_pos_rev : forall r1 r2,
  r1 / r2 > 0 -> r2 > 0 -> r1 > 0.
Proof.
  intros r1 r2 H1 H2. pose proof Rtotal_order r1 0 as [H3 | [H3 | H3]]; try nra.
  pose proof Rdiv_neg_pos r1 r2 ltac:(lra) ltac:(lra). nra.
Qed.

Lemma Rdiv_neg_pos_rev : forall r1 r2,
  r1 / r2 < 0 -> r2 > 0 -> r1 < 0.
Proof.
  intros r1 r2 H1 H2. pose proof Rtotal_order r1 0 as [H3 | [H3 | H3]]; try nra.
  pose proof Rdiv_pos_pos r1 r2 ltac:(lra) ltac:(lra). nra.
Qed.

Lemma Rdiv_pos_neg_rev : forall r1 r2,
  r1 / r2 < 0 -> r2 < 0 -> r1 > 0.
Proof.
  intros r1 r2 H1 H2. pose proof Rtotal_order r1 0 as [H3 | [H3 | H3]]; try nra.
  pose proof Rdiv_neg_neg r1 r2 ltac:(lra) ltac:(lra). nra.
Qed.

Lemma Rdiv_pos_neg_rev' : forall r1 r2,
  r1 / r2 > 0 -> r2 < 0 -> r1 < 0.
Proof.
  intros r1 r2 H1 H2. pose proof Rtotal_order r1 0 as [H3 | [H3 | H3]]; try nra.
  pose proof Rdiv_pos_neg r1 r2 ltac:(lra) ltac:(lra). nra.
Qed.