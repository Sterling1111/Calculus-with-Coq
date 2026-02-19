From Lib Require Import Imports Notations.

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

Lemma is_natural_pow : forall r n,
  is_natural r -> is_natural (r ^ n).
Proof.
  intros r n H1. destruct H1 as [k H1]. exists (k ^ n)%nat. rewrite H1. rewrite pow_INR. reflexivity.
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

Lemma Rdiv_nonneg_nonneg : forall r1 r2,
  r1 >= 0 -> r2 > 0 -> r1 / r2 >= 0.
Proof.
  intros r1 r2 H1 H2.
  pose proof Rtotal_order r1 0 as [H3 | [H3 | H3]]; try nra.
  pose proof Rdiv_pos_pos r1 r2 ltac:(lra) ltac:(lra). nra.
Qed.  

Lemma floor_spec : ∀ x : R,
  x >= 0 ->
  ⌊ x ⌋ <= x < ⌊ x ⌋ + 1.
Proof.
  intros x H1.
  unfold Nfloor.
  rewrite INR_IZR_INZ.
  generalize (base_Int_part x). intros [H2 H3].
  rewrite Z2Nat.id; [split; lra | ].
  assert (H4 : IZR (Int_part x) > -1) by lra.
  apply lt_IZR in H4. lia.
Qed.

Lemma ceil_spec : forall x : R,
  x > 0 ->
  ⌈ x ⌉ - 1 <= x < ⌈ x ⌉.
Proof.
  intros x H1.
  unfold Nceil.
  rewrite INR_IZR_INZ.
  generalize (archimed x); intros [H2 H3].
  rewrite Z2Nat.id; [ split; lra |].
  apply le_IZR; lra.
Qed.

Lemma floor_unique : forall (x : R) (n : nat),
  x >= 0 ->
  n <= x < n + 1 ->
  ⌊ x ⌋ = n.
Proof.
  intros x n H1 [H2 H3].
  unfold Nfloor.
  apply Nat2Z.inj.
  rewrite Z2Nat.id.
  - symmetry.
    apply Int_part_spec.
    rewrite <- INR_IZR_INZ.
    split; lra.
  - generalize (base_Int_part x); intros [H4 H5].
    assert (H6 : (-1 < Int_part x)%Z).
    { apply lt_IZR. lra. }
    lia.
Qed.

Lemma ceil_unique : forall (x : R) (n : nat),
  x > 0 ->
  n - 1 <= x < n ->
  ⌈ x ⌉ = n.
Proof.
  intros x n H1 [H2 H3].
  unfold Nceil.
  apply Nat2Z.inj.
  rewrite Z2Nat.id.
  - symmetry. apply tech_up; rewrite <- INR_IZR_INZ; lra.
  - apply le_IZR.
    transitivity x; [lra |].
    generalize (archimed x); intros [H4 H5]. lra.
Qed.

Lemma floor_INR : forall r, is_natural r -> INR ⌊r⌋ = r.
Proof.
  intros r [k H1].
  rewrite H1. unfold Nfloor. rewrite Int_part_INR.
  rewrite Nat2Z.id; auto.
Qed.

Lemma floor_INR_id : forall n : nat, ⌊INR n⌋ = n.
Proof.
  intros n. unfold Nfloor. rewrite Int_part_INR.
  rewrite Nat2Z.id; auto.
Qed.

Lemma floor_power_succ_div : forall n b, b > 1 -> is_natural b -> ⌊b ^ (S n) / b⌋ = ⌊b ^ n⌋.
Proof.
  intros n b H1 [k H2]. assert ((k = 0)%nat \/ (k > 0)%nat) as [H3 | H3] by lia.
  - subst. replace 1 with (INR 1) in H1 by auto. apply INR_lt in H1. lia.
  - rewrite H2, <- tech_pow_Rmult. 
    replace (INR k * INR k ^ n / INR k) with (INR k ^ n) by (field; lra). auto.
Qed.

Lemma floor_power_succ_ge_base : forall b k, 
  b > 1 -> is_natural b -> ⌊b ^ (S k)⌋ >= b.
Proof.
  intros b k H1 H2.
  induction k as [| k IH].
  - simpl. rewrite floor_INR. 2: { rewrite Rmult_1_r; auto. } lra.
  - rewrite floor_INR in *; try apply is_natural_pow; auto. simpl in *; nra.
Qed.

Lemma floor_floor : forall r, r >= 0 -> ⌊⌊r⌋⌋ = ⌊r⌋.
Proof.
  intros r H1.
  apply floor_unique; try lra.
  pose proof floor_spec r H1 as [H2 H3].
  pose proof pos_INR (⌊r⌋) as H4.
  lra.
Qed.

Lemma pow_unbounded : forall b M : R, b > 1 -> exists n : nat, b ^ n >= M.
Proof.
  intros b M H1.
  destruct (Pow_x_infinity b ltac:(solve_R) M) as [N H2].
  exists N.
  specialize (H2 N ltac:(solve_R)).
  rewrite Rabs_right in H2; solve_R.
  apply Rle_ge. apply pow_le. lra.
Qed.

Lemma floor_gt_0 : ∀ x : R, x ≥ 1 → ⌊x⌋ > 0.
Proof.
  intros x H1. replace 0 with (INR 0) by auto.
  destruct (floor_spec x ltac:(lra)) as [H2 H3].
  solve_R.
Qed.

Lemma Rdiv_ge_0 : forall a b,
  a >= 0 -> b > 0 -> a / b >= 0.
Proof.
  intros a b H1 H2.
  pose proof Rtotal_order a 0 as [H3 | [H3 | H3]]; try nra.
  pose proof Rdiv_pos_pos a b ltac:(lra) ltac:(lra). nra.
Qed.

Lemma Rle_div_l : ∀ a b c, c > 0 → a / c ≤ b ↔ a ≤ b * c.
Proof.
  intros a b c H.
  split; intros H1.
  - apply Rmult_le_reg_r with (/ c); [apply Rinv_0_lt_compat; lra |].
    rewrite Rmult_assoc, Rinv_r, Rmult_1_r; nra.
  - apply Rmult_le_reg_r with c; [lra |].
    rewrite Rdiv_def, Rmult_assoc, Rinv_l, Rmult_1_r; nra.
Qed.

Lemma Rle_div_r : ∀ a b c, c > 0 → a ≤ b / c ↔ a * c ≤ b.
Proof.
  intros a b c H.
  split; intros H1.
  - apply Rmult_le_reg_r with (/ c); [apply Rinv_0_lt_compat; lra |].
    rewrite Rmult_assoc, Rinv_r, Rmult_1_r; nra.
  - apply Rmult_le_reg_r with c; [lra |].
    rewrite Rdiv_def, Rmult_assoc, Rinv_l, Rmult_1_r; nra.
Qed.

Lemma Rlt_div_l : ∀ a b c, c > 0 → a / c < b ↔ a < b * c.
Proof.
  intros a b c H.
  split; intros H1.
  - apply Rmult_lt_reg_r with (/ c); [apply Rinv_0_lt_compat; lra |].
    rewrite Rmult_assoc, Rinv_r, Rmult_1_r; nra.
  - apply Rmult_lt_reg_r with c; [lra |].
    rewrite Rdiv_def, Rmult_assoc, Rinv_l, Rmult_1_r; nra.
Qed.

Lemma floor_div_general : forall n d : nat, 
  (d > 0)%nat -> 
  (n / d)%nat = ⌊INR n / INR d⌋.
Proof.
  intros n d H1.
  symmetry.
  apply floor_unique.
  - apply Rdiv_ge_0; solve_R. apply Rle_ge, pos_INR.
  - split.
    + apply Rle_div_r; solve_R.
      rewrite <- mult_INR. apply le_INR.
      rewrite Nat.mul_comm.
      apply Nat.Div0.mul_div_le; auto.
    + apply Rlt_div_l; solve_R.
      rewrite Rmult_plus_distr_r, Rmult_1_l, <- mult_INR, <- plus_INR.
      Set Printing Coercions.
      apply lt_INR.
      rewrite Nat.mul_comm.
      assert (H2 : (d > 0)%nat).
      { 
        replace 0 with (INR 0) in H1 by reflexivity.
        apply INR_lt in H1. 
        exact H1. 
      }
      pose proof Nat.div_mod n d ltac:(lia) as H3.
      pose proof Nat.mod_upper_bound n d ltac:(lia) as H4.
      lia.
Qed.

Lemma Rle_not_gt : forall a b,
  ~(a > b) <-> a <= b.
Proof.
  intros a b. nra.
Qed.

Lemma INR_ge : forall n m : nat,
  INR n >= INR m <-> (n >= m)%nat.
Proof.
  intros n m. split.
  - intros H1. apply Rge_le, INR_le in H1. lia.
  - intros H1. solve_R.
Qed.

Lemma iter_ineq_on_powers
  (a b c1 c2 : R) (f : nat -> R)
  (M n j : nat) :
  a ≥ 1 ->
  b > 1 ->
  c1 > 0 ->
  is_natural b ->
  (forall m : nat, m ≥ c2 -> a * f ⌊m / b⌋ ≤ c1 * f m) ->
  b ^ M ≥ Rmax c2 b ->
  (M > 0)%nat ->
  (0 <= j <= n - M - 1)%nat ->
  a ^ j * f ⌊b ^ (n - j)⌋ ≤ c1 ^ j * f ⌊b ^ n⌋.
Proof.
  intros H1 H2 H0 H3 H4 H5 H6 H7.
  induction j as [| k IH].
  - rewrite Nat.sub_0_r. lra.
  - assert (H8 : (0 <= k <= n - M - 1)%nat) by lia.
    specialize (IH H8). pose proof H3 as H3'.
    destruct H3 as [nb H3].
  assert (H9 : (n - k = S (n - S k))%nat) by lia.
  assert (H10 : is_natural (b ^ (n - k))).
  { exists (nb ^ (n - k))%nat. rewrite H3, pow_INR. reflexivity. }
  assert (H11 : INR ⌊b ^ (n - k)⌋ >= c2).
  { rewrite floor_INR; try exact H10.
    apply Rle_ge, Rle_trans with (b ^ M); [ solve_R | ]. 
    apply Rle_pow; try lra. lia. }
  specialize (H4 _ H11).
  rewrite floor_INR in H4; try exact H10.
  rewrite H9 in H4.
  rewrite floor_power_succ_div in H4; auto.
  apply Rle_trans with (a ^ k * (c1 * f ⌊b ^ (n - k)⌋)).
  + replace (a ^ S k * f ⌊b ^ (n - S k)⌋) with (a ^ k * (a * f ⌊b ^ (n - S k)⌋)) by (simpl; lra).
    apply Rmult_le_compat_l. apply pow_le. lra.
    rewrite H9. auto.
  + replace (a ^ k * (c1 * f ⌊b ^ (n - k)⌋)) with (c1 * (a ^ k * f ⌊b ^ (n - k)⌋)) by lra.
    replace (c1 ^ S k * f ⌊b ^ n⌋) with (c1 * (c1 ^ k * f ⌊b ^ n⌋)) by (simpl; lra).
    apply Rmult_le_compat_l; lra.
Qed.

Lemma no_natural_between : forall (n : ℕ) r,
  n < r < (S n) -> ~ is_natural r.
Proof.
  intros n r [H1 H2] [k H3]. rewrite H3 in *. apply INR_lt in H1. apply INR_lt in H2. lia.
Qed.

Lemma no_integer_between : forall (n : ℤ) r,
  n < r < n + 1 -> ~ is_integer r.
Proof.
  intros n r [H1 H2] [k H3]. rewrite H3 in *. apply lt_IZR in H1. rewrite <- plus_IZR in H2. apply lt_IZR in H2. lia.
Qed.

Lemma Rabs_div : forall r1 r2,
  |r1 / r2| = |r1| / |r2|.
Proof.
  intros r1 r2.
  destruct (Rtotal_order r1 r2) as [H1 | [H1 | H1]];
  destruct (Rtotal_order r2 0) as [H2 | [H2 | H2]]; 
  destruct (Rtotal_order r1 0) as [H3 | [H3 | H3]];
  subst; try solve [solve_R].
  - solve_R. pose proof Rdiv_neg_neg r1 r2 ltac:(lra) ltac:(lra). nra.
  - repeat rewrite Rabs_R0, Rdiv_0_r; reflexivity.
  - pose proof Rdiv_neg_pos r1 r2 ltac:(lra) ltac:(lra). solve_R.
  - pose proof Rdiv_pos_pos r1 r2 ltac:(lra) ltac:(lra). solve_R.
  - rewrite Rdiv_diag; solve_R.
  - rewrite Rabs_R0, Rdiv_0_r. solve_R.
  - rewrite Rdiv_diag; solve_R.
  - pose proof Rdiv_neg_neg r1 r2 ltac:(lra) ltac:(lra). solve_R.
  - pose proof Rdiv_pos_neg r1 r2 ltac:(lra) ltac:(lra). solve_R.
  - repeat rewrite Rabs_R0, Rdiv_0_r; reflexivity.
  - pose proof Rdiv_pos_pos r1 r2 ltac:(lra) ltac:(lra). solve_R.
Qed.