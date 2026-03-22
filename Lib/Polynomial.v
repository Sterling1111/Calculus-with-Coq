From Lib Require Import Imports Reals_util Sums Continuity Limit Notations Products Derivative.
Import LimitNotations SumNotations ProductNotations DerivativeNotations.

Open Scope R_scope.

Local Notation length := List.length.

Definition polynomial (l : list R) : R -> R :=
  fun x => sum_f 0 (length l - 1) (fun i => nth i l 0 * x^(length l - 1 - i)).

Definition leading_coefficient (l : list R) : R := nth 0 l 0.

Fixpoint degree (l : list R) : nat :=
  match l with
  | [] => 0
  | h :: t => if Req_EM_T h 0 then degree t else length l - 1
  end.

Lemma poly_nil : forall x, polynomial ([] : list R) x = 0.
Proof.
  intro; compute. rewrite Rmult_1_r. reflexivity.
Qed.

Lemma poly_cons : forall h t x, polynomial (h :: t) x = h * x^(length t) + polynomial t x.
Proof.
  intros h t x. unfold polynomial. assert (length t = 0 \/ length t > 0)%nat as [H1 | H1] by lia.
  - rewrite length_zero_iff_nil in H1. subst; simpl; repeat rewrite sum_f_0_0; lra.
  - replace (length (h :: t) - 1)%nat with (length t) by (simpl; lia). rewrite sum_f_nth_cons_8; try lia.
    replace (x ^ (length t - 0) * h) with (h * x ^ (length t)). 2 : { rewrite Nat.sub_0_r; lra. }
    apply Rplus_eq_compat_l. apply sum_f_equiv; try lia. intros k H2.
    replace (length t - (k + 1))%nat with (length t - 1 - k)%nat by lia. reflexivity.
Qed.

Lemma continuous_at_polynomial : forall l a,
  continuous_at (polynomial l) a.
Proof.
  intros l a. induction l as [| h t IH].
  - replace (polynomial []) with (fun _ : ℝ => 0).
    2 : { extensionality x. rewrite poly_nil. reflexivity. }
    apply continuous_at_const.
  - replace (polynomial (h :: t)) with (fun x : ℝ => h * x^(length t) + polynomial t x).
    2 : { extensionality x. rewrite poly_cons. reflexivity. }
    apply continuous_at_plus; auto.
    apply continuous_at_mult.
    * apply continuous_at_const.
    * apply continuous_at_pow.
Qed.

Theorem continuous_polynomial : forall l,
  continuous (polynomial l).
Proof.
  intros l a. apply continuous_at_polynomial.
Qed.

Lemma continuous_on_polynomial : forall l D,
  continuous_on (polynomial l) D.
Proof.
  intros l D a H1. induction l as [| h t IH].
  - replace (polynomial []) with (fun _ : ℝ => 0).
    2 : { extensionality x. rewrite poly_nil. reflexivity. }
    apply limit_on_const.
  - replace (polynomial (h :: t)) with (fun x : ℝ => h * x^(length t) + polynomial t x).
    2 : { extensionality x. rewrite poly_cons. reflexivity. }
    apply limit_on_plus.
    + apply limit_on_mult.
      * apply limit_on_const.
      * apply limit_on_pow. apply limit_on_id.
    + apply IH. 
Qed.

Lemma poly_shift : forall l c x,
  polynomial (l ++ [c]) x = x * polynomial l x + c.
Proof.
  intros.
  destruct l as [|a l].
  - simpl. unfold polynomial. simpl. repeat rewrite sum_f_0_0. lra.
  - unfold polynomial.
    rewrite length_app. 
    replace (length (a :: l) + length [c] - 1)%nat with (S (length l)) by (simpl; lia).
    replace (length (a :: l)) with (S (length l)) by (simpl; lia).
    rewrite sum_f_i_Sn_f; try lia.
    rewrite Rplus_comm.
    rewrite (Rplus_comm (x * _)).
    f_equal.
    + rewrite app_nth2. 2 : { simpl; lia. }
      rewrite Nat.sub_diag. simpl. rewrite Nat.sub_diag. lra.
    + rewrite r_mult_sum_f_i_n_f_l.
      replace (S (length l) - 1)%nat with (length l) by lia.
      apply sum_f_equiv; try lia.
      intros k H2.
      rewrite app_nth1. 2 : { simpl; lia. }
      replace (S (length l) - k)%nat with (S (length l - k))%nat by lia.
      simpl. lra.
Qed.

Lemma limit_poly_offset : forall l a,
  ⟦ lim a ⟧ (fun x => polynomial l (x - a)) = polynomial l 0.
Proof.
  intros l a.
  destruct l as [|c l] using rev_ind.
  - simpl. replace (λ x : ℝ, polynomial [] (x - a)) with (λ x : ℝ, 0).
    2 : { extensionality x. rewrite poly_nil. reflexivity. }
    rewrite poly_nil. apply limit_const.
  - rewrite !poly_shift.
    apply limit_eq with (f1 := fun x => (x - a) * polynomial l (x - a) + c).
    + exists 1. split; try lra. intros x H1. rewrite poly_shift. reflexivity.
    + apply limit_plus_const. apply limit_mult; auto.
      replace 0 with (a - a) by lra. apply limit_minus; [apply limit_id | apply limit_const].
Qed.

Lemma poly_decompose : forall l, exists t c, 
  (forall x, polynomial l x = x * polynomial t x + c) /\
  (length t = pred (length l)).
Proof.
  intros l. induction l as [| c l' _] using rev_ind.
  - exists [], 0. split.
    + intros x. rewrite poly_nil. lra.
    + simpl. reflexivity.
  - exists l', c. split.
    + intros x. rewrite poly_shift. reflexivity.
    + rewrite length_app. simpl. lia.
Qed.

Fixpoint poly_add_rev (l1 l2 : list R) : list R :=
  match l1, l2 with
  | [], _ => l2
  | _, [] => l1
  | h1 :: t1, h2 :: t2 => (h1 + h2) :: poly_add_rev t1 t2
  end.

Definition poly_scale (c : R) (l : list R) : list R :=
  map (λ a, c * a) l.

Fixpoint poly_mul_rev (l1 l2 : list R) : list R :=
  match l1 with
  | [] => []
  | h :: t => poly_add_rev (poly_scale h l2) (0 :: poly_mul_rev t l2)
  end.

Definition poly_opp (l : list R) : list R :=
  map (λ c, - c) l.

Definition poly_add (l1 l2 : list R) : list R :=
  rev (poly_add_rev (rev l1) (rev l2)).

Definition poly_sub (l1 l2 : list R) : list R :=
  poly_add l1 (poly_opp l2).

Definition poly_mul (l1 l2 : list R) : list R :=
  rev (poly_mul_rev (rev l1) (rev l2)).

Lemma poly_add_rev_nil_r : forall l, poly_add_rev l [] = l.
Proof.
  destruct l; reflexivity.
Qed.

Lemma poly_add_nil_r : forall l, poly_add l [] = l.
Proof.
  intros l. unfold poly_add. simpl.
  rewrite poly_add_rev_nil_r.
  apply rev_involutive.
Qed.

Lemma poly_add_nil_l : forall l, poly_add [] l = l.
Proof.
  intros l. unfold poly_add. simpl.
  apply rev_involutive.
Qed.

Lemma poly_add_rev_sym : forall l1 l2, poly_add_rev l1 l2 = poly_add_rev l2 l1.
Proof.
  induction l1 as [| h1 t1 H1]; intros l2.
  - destruct l2; reflexivity.
  - destruct l2 as [| h2 t2].
    + reflexivity.
    + simpl. f_equal.
      * apply Rplus_comm.
      * apply H1.
Qed.

Lemma poly_add_sym : forall l1 l2, poly_add l1 l2 = poly_add l2 l1.
Proof.
  intros l1 l2. unfold poly_add.
  rewrite poly_add_rev_sym.
  reflexivity.
Qed.

Lemma eval_poly_add_rev_helper : forall L1 L2 x,
  polynomial (rev (poly_add_rev L1 L2)) x = polynomial (rev L1) x + polynomial (rev L2) x.
Proof.
  induction L1 as [| h1 t1 IH]; intros L2 x.
  - simpl. rewrite poly_nil. lra.
  - destruct L2 as [| h2 t2].
    + simpl. rewrite poly_nil. lra.
    + simpl. repeat rewrite poly_shift.
      rewrite IH. lra.
Qed.

Lemma eval_poly_add : forall l1 l2 x,
  polynomial (poly_add l1 l2) x = polynomial l1 x + polynomial l2 x.
Proof.
  intros l1 l2 x. unfold poly_add.
  rewrite eval_poly_add_rev_helper.
  repeat rewrite rev_involutive.
  reflexivity.
Qed.

Lemma eval_poly_opp : forall l x,
  polynomial (poly_opp l) x = - polynomial l x.
Proof.
  intros l x. induction l as [| c l' IH] using rev_ind.
  - simpl. repeat rewrite poly_nil. lra.
  - unfold poly_opp. rewrite map_app. simpl.
    change (map (λ c0, - c0) l') with (poly_opp l').
    repeat rewrite poly_shift.
    rewrite IH. lra.
Qed.

Lemma eval_poly_sub : forall l1 l2 x,
  polynomial (poly_sub l1 l2) x = polynomial l1 x - polynomial l2 x.
Proof.
  intros l1 l2 x. unfold poly_sub.
  rewrite eval_poly_add, eval_poly_opp. lra.
Qed.

Lemma eval_poly_scale : forall c l x,
  polynomial (poly_scale c l) x = c * polynomial l x.
Proof.
  intros c l x. induction l as [| h t IH] using rev_ind.
  - unfold poly_scale. simpl. repeat rewrite poly_nil. lra.
  - unfold poly_scale in *. rewrite map_app. simpl.
    repeat rewrite poly_shift. rewrite IH. lra.
Qed.

Lemma poly_scale_rev : forall c l,
  rev (poly_scale c l) = poly_scale c (rev l).
Proof.
  intros c l. unfold poly_scale. rewrite map_rev; auto.
Qed.

Lemma eval_poly_mul_rev_helper : forall L1 L2 x,
  polynomial (rev (poly_mul_rev L1 L2)) x = polynomial (rev L1) x * polynomial (rev L2) x.
Proof.
  induction L1 as [| h1 t1 IH]; intros L2 x.
  - simpl. repeat rewrite poly_nil. lra.
  - simpl. rewrite eval_poly_add_rev_helper.
    rewrite poly_scale_rev, eval_poly_scale.
    repeat rewrite poly_shift.
    simpl rev.
    rewrite poly_shift.
    rewrite IH.
    lra.
Qed.

Lemma eval_poly_mul : forall l1 l2 x,
  polynomial (poly_mul l1 l2) x = polynomial l1 x * polynomial l2 x.
Proof.
  intros l1 l2 x. unfold poly_mul.
  rewrite eval_poly_mul_rev_helper.
  repeat rewrite rev_involutive.
  reflexivity.
Qed.

Definition is_zero_poly (l : list R) : Prop :=
  Forall (λ c, c = 0) l.

Lemma is_zero_poly_eval : forall l x,
  is_zero_poly l -> polynomial l x = 0.
Proof.
  intros l x H1. induction l as [| h t H2].
  - apply poly_nil.
  - inversion H1; subst.
    rewrite poly_cons.
    rewrite H2; auto.
    lra.
Qed.

Lemma eval_zero_is_zero_poly : forall l,
  (forall x, polynomial l x = 0) -> is_zero_poly l.
Proof.
  intros l. induction l as [| c l' IH] using rev_ind.
  - intros H1. apply Forall_nil.
  - intros H1.
    assert (H2 : c = 0).
    { pose proof (H1 0) as H2. rewrite poly_shift in H2. lra. }
    unfold is_zero_poly in *. rewrite Forall_app. split.
    + apply IH. intros x.
      destruct (Rtotal_order x 0) as [H3 | [H3 | H3]].
      * pose proof (H1 x) as H4. rewrite poly_shift, H2 in H4. nra.
      * subst x. pose proof (limit_poly_offset l' 0) as H4.
        replace (λ x : ℝ, polynomial l' (x - 0)) with (polynomial l') in H4.
        2 : { extensionality y. replace (y - 0) with y by lra. reflexivity. }
        assert (H5 : ⟦ lim 0 ⟧ (polynomial l') = 0).
        { 
          apply limit_eq with (f1 := λ _ : ℝ, 0).
          - exists 1. split; [lra |]. intros y H5.
            pose proof (H1 y) as H6. rewrite poly_shift, H2 in H6. solve_R.
          - apply limit_const. 
        }
        apply limit_unique with (f := polynomial l') (a := 0); auto.
      * pose proof (H1 x) as H4. rewrite poly_shift, H2 in H4. nra.
    + apply Forall_cons; auto.
Qed.

Lemma poly_equiv_iff_sub_zero : forall l1 l2,
  (forall x, polynomial l1 x = polynomial l2 x) <-> is_zero_poly (poly_sub l1 l2).
Proof.
  intros l1 l2. split.
  - intros H1. apply eval_zero_is_zero_poly.
    intros x. rewrite eval_poly_sub. rewrite H1. lra.
  - intros H1. intros x.
    pose proof is_zero_poly_eval _ x H1 as H2.
    rewrite eval_poly_sub in H2. lra.
Qed.

Lemma is_zero_poly_dec : forall l, is_zero_poly l \/ ~ is_zero_poly l.
Proof.
  intros l. induction l as [| h t H1].
  - left. apply Forall_nil.
  - destruct H1 as [H2 | H2].
    + destruct (Req_EM_T h 0) as [H3 | H3].
      * left. apply Forall_cons; auto.
      * right. intros H4. inversion H4. lra.
    + right. intros H3. inversion H3. auto.
Qed.

Lemma poly_const_eval : forall m x, polynomial [m] x = m.
Proof.
  intros. rewrite poly_cons, poly_nil. simpl. lra.
Qed.

Lemma degree_app_c_zero : forall l c, is_zero_poly l -> degree (l ++ [c]) = 0%nat.
Proof.
  intros l c H1. induction l as [| h t H2].
  - simpl. destruct (Req_EM_T c 0); reflexivity.
  - inversion H1; subst. simpl. destruct (Req_EM_T 0 0) as [_ | H3]; auto. lra.
Qed.

Lemma degree_app_c_not_zero : forall l c, ~ is_zero_poly l -> degree (l ++ [c]) = S (degree l).
Proof.
  intros l c H1. induction l as [| h t H2].
  - exfalso. apply H1. apply Forall_nil.
  - simpl. destruct (Req_EM_T h 0) as [H3 | H3].
    + subst h. rewrite H2. reflexivity. intros H4. apply H1. apply Forall_cons; auto.
    + rewrite length_app. simpl. lia.
Qed.

Lemma degree_shifted_le : forall R_poly B c,
  (degree R_poly < degree B \/ is_zero_poly R_poly)%nat ->
  (degree (R_poly ++ [c]) <= degree B)%nat.
Proof.
  intros R_poly B c H1.
  destruct (is_zero_poly_dec R_poly) as [H2 | H2].
  - rewrite degree_app_c_zero; auto. lia.
  - rewrite degree_app_c_not_zero; auto. destruct H1 as [H3 | H3].
    + lia.
    + contradiction.
Qed.

Fixpoint lead_coeff (l : list R) : R :=
  match l with
  | [] => 0
  | h :: t => if Req_EM_T h 0 then lead_coeff t else h
  end.

Lemma lead_coeff_zero_iff : forall l,
  is_zero_poly l <-> lead_coeff l = 0.
Proof.
  intros l; split.
  - induction l as [| h t IH].
    + reflexivity.
    + intros H. inversion H; subst. simpl. destruct (Req_EM_T 0 0) as [H1|H1].
      * apply IH; auto.
      * lra.
  - induction l as [| h t IH].
    + intros _. apply Forall_nil.
    + simpl. destruct (Req_EM_T h 0) as [H1|H1].
      * intros H2. apply Forall_cons; auto. apply IH; auto.
      * lra.
Qed.

Lemma degree_poly_scale : forall m l,
  m <> 0 -> degree (poly_scale m l) = degree l.
Proof.
  intros m l H; induction l as [| h t IH].
  - reflexivity.
  - simpl. unfold poly_scale in *. simpl.
    destruct (Req_EM_T (m * h) 0) as [H1 | H1]; 
    destruct (Req_EM_T h 0) as [H2 | H2]; auto; try nra.
    rewrite length_map. reflexivity.
Qed.

Lemma lead_coeff_poly_scale : forall m l,
  lead_coeff (poly_scale m l) = m * lead_coeff l.
Proof.
  intros m l; induction l as [| h t IH].
  - simpl. lra.
  - simpl. unfold poly_scale in *. simpl. destruct (Req_EM_T (m * h) 0) as [H1 | H1]; destruct (Req_EM_T h 0) as [H2 | H2].
    + exact IH.
    + rewrite IH; destruct (Rmult_integral _ _ H1) as [H3|H3].
      * rewrite H3; lra.
      * contradiction.
    + rewrite H2 in H1; rewrite Rmult_0_r in H1; lra.
    + reflexivity.
Qed.

Lemma degree_le_length : forall l, (degree l <= length l - 1)%nat.
Proof.
  induction l as [| h t IH]; simpl. lia.
  destruct (Req_EM_T h 0). destruct t as [|r t]; simpl in *; try lia. lia.
Qed.

Lemma poly_add_rev_length_eq : forall l1 l2,
  length l1 = length l2 -> length (poly_add_rev l1 l2) = length l1.
Proof.
  induction l1 as [| h1 t1 IH]. destruct l2; simpl; auto.
  destruct l2; intros H; simpl in *; try lia. f_equal. apply IH. lia.
Qed.

Lemma poly_opp_length : forall l, length (poly_opp l) = length l.
Proof. induction l; [reflexivity | simpl; f_equal; auto]. Qed.

Lemma poly_sub_length_eq : forall l1 l2,
  length l1 = length l2 -> length (poly_sub l1 l2) = length l1.
Proof.
  intros. unfold poly_sub, poly_add. rewrite length_rev, poly_add_rev_length_eq.
  - rewrite length_rev. reflexivity.
  - repeat rewrite length_rev. rewrite H. rewrite <- poly_opp_length. reflexivity.
Qed.

Lemma poly_add_rev_app_eq_len : forall l1 l2 c1 c2,
  length l1 = length l2 ->
  poly_add_rev (l1 ++ [c1]) (l2 ++ [c2]) = poly_add_rev l1 l2 ++ [c1 + c2].
Proof.
  induction l1 as [| h1 t1 IH]. intros l2 c1 c2 H. destruct l2; simpl in *; try lia. reflexivity.
  intros l2 c1 c2 H. destruct l2 as [| h2 t2]; simpl in *; try lia. f_equal. apply IH. lia.
Qed.

Lemma poly_add_eq_len : forall l1 l2 c1 c2,
  length l1 = length l2 -> poly_add (c1 :: l1) (c2 :: l2) = (c1 + c2) :: poly_add l1 l2.
Proof.
  intros l1 l2 c1 c2 H. unfold poly_add. simpl. rewrite poly_add_rev_app_eq_len.
  - rewrite rev_app_distr. simpl. reflexivity.
  - repeat rewrite length_rev. exact H.
Qed.

Lemma poly_sub_eq_len : forall l1 l2 c1 c2,
  length l1 = length l2 -> poly_sub (c1 :: l1) (c2 :: l2) = (c1 - c2) :: poly_sub l1 l2.
Proof.
  intros l1 l2 c1 c2 H. unfold poly_sub. change (poly_opp (c2 :: l2)) with (- c2 :: poly_opp l2).
  rewrite poly_add_eq_len; auto. rewrite H, <- poly_opp_length. reflexivity.
Qed.

Lemma degree_cons_0 : forall l, degree (0 :: l) = degree l.
Proof. intros l. simpl. destruct (Req_EM_T 0 0); auto. lra. Qed.

Lemma lead_coeff_cons_0 : forall l, lead_coeff (0 :: l) = lead_coeff l.
Proof. intros l. simpl. destruct (Req_EM_T 0 0); auto. lra. Qed.

Lemma is_zero_poly_cons_0 : forall l, is_zero_poly (0 :: l) <-> is_zero_poly l.
Proof.
  intros l. split; intros H; inversion H; subst; auto. apply Forall_cons; auto. unfold is_zero_poly in *.
  apply Forall_cons; [lra | exact H].
Qed.

Lemma degree_poly_sub_eq_len : forall l1 l2,
  length l1 = length l2 -> degree l1 = degree l2 -> lead_coeff l1 = lead_coeff l2 ->
  (degree (poly_sub l1 l2) < degree l1 \/ is_zero_poly (poly_sub l1 l2))%nat.
Proof.
  induction l1 as [| h1 t1 IH].
  - intros l2 Hlen Hdeg Hlead. destruct l2; simpl in *; try lia.
    right. unfold poly_sub, poly_add, poly_add_rev, poly_opp, rev; simpl. apply Forall_nil.
  - intros l2 Hlen Hdeg Hlead. destruct l2 as [| h2 t2]; simpl in *; try lia.
    assert (Hlen' : length t1 = length t2) by lia.
    rewrite poly_sub_eq_len; auto. simpl in Hdeg, Hlead.
    destruct (Req_EM_T h1 0) as [H1 | H1]; destruct (Req_EM_T h2 0) as [H2 | H2].
    + rewrite H1, H2. replace (0 - 0) with 0 by lra.
      rewrite degree_cons_0, is_zero_poly_cons_0. apply IH; auto.
    + subst h1. destruct t1 as [| h1' t1'].
      * simpl in Hlead; lra.
      * pose proof (degree_le_length (h1' :: t1')). simpl in *. lia.
    + subst h2. destruct t2 as [| h2' t2'].
      * simpl in Hlead; lra.
      * pose proof (degree_le_length (h2' :: t2')). simpl in *. lia.
    + replace (h1 - h2) with 0 by lra.
      destruct (is_zero_poly_dec (poly_sub t1 t2)) as [Hz | Hnz].
      * right. apply Forall_cons; auto.
      * left. rewrite degree_cons_0. pose proof (degree_le_length (poly_sub t1 t2)) as Hle.
        rewrite poly_sub_length_eq in Hle; auto.
        destruct t1 as [| h1' t1'].
        -- destruct t2; [ | simpl in *; lia]. unfold poly_sub, poly_add, poly_add_rev, poly_opp, rev in Hnz; simpl in Hnz. exfalso; apply Hnz. apply Forall_nil.
        -- simpl in *. lia.
Qed.

Lemma poly_add_rev_app_c_l : forall l1 l2 c,
  (length l1 >= length l2)%nat -> poly_add_rev (l1 ++ [c]) l2 = poly_add_rev l1 l2 ++ [c].
Proof.
  induction l1 as [| h1 t1 IH].
  - intros l2 c H. destruct l2; simpl in *; try lia. reflexivity.
  - intros l2 c H. destruct l2 as [| h2 t2]. simpl. reflexivity.
    simpl in *. f_equal. apply IH. lia.
Qed.

Lemma poly_add_rev_app_c_r : forall l1 l2 c,
  (length l2 >= length l1)%nat -> poly_add_rev l1 (l2 ++ [c]) = poly_add_rev l1 l2 ++ [c].
Proof.
  induction l1 as [| h1 t1 IH].
  - simpl. reflexivity.
  - intros l2 c H. destruct l2 as [| h2 t2]; simpl in *; try lia. f_equal. apply IH. lia.
Qed.

Lemma poly_add_pad_l : forall l1 l2 c,
  (length l1 >= length l2)%nat -> poly_add (c :: l1) l2 = c :: poly_add l1 l2.
Proof.
  intros l1 l2 c H. unfold poly_add. simpl. rewrite poly_add_rev_app_c_l; auto.
  rewrite rev_app_distr. simpl. reflexivity. repeat rewrite length_rev. assumption.
Qed.

Lemma poly_add_pad_r : forall l1 l2 c,
  (length l2 >= length l1)%nat -> poly_add l1 (c :: l2) = c :: poly_add l1 l2.
Proof.
  intros l1 l2 c H. unfold poly_add. simpl. rewrite poly_add_rev_app_c_r; auto.
  rewrite rev_app_distr. simpl. reflexivity. repeat rewrite length_rev. assumption.
Qed.

Lemma poly_sub_pad_l : forall l1 l2,
  (length l1 >= length l2)%nat -> poly_sub (0 :: l1) l2 = 0 :: poly_sub l1 l2.
Proof.
  intros l1 l2 H. unfold poly_sub. rewrite poly_add_pad_l; auto.
  rewrite poly_opp_length. assumption.
Qed.

Lemma poly_sub_pad_r : forall l1 l2,
  (length l2 >= length l1)%nat -> poly_sub l1 (0 :: l2) = -0 :: poly_sub l1 l2.
Proof.
  intros l1 l2 H. unfold poly_sub. change (poly_opp (0 :: l2)) with (-0 :: poly_opp l2).
  rewrite poly_add_pad_r; auto. rewrite poly_opp_length. assumption.
Qed.

Lemma degree_cons_neg_0 : forall l, degree (-0 :: l) = degree l.
Proof. intros l. simpl. destruct (Req_EM_T (-0) 0); auto. lra. Qed.

Lemma is_zero_poly_cons_neg_0 : forall l, is_zero_poly (-0 :: l) <-> is_zero_poly l.
Proof.
  intros l. split; intros H; inversion H; subst; auto. apply Forall_cons; auto; lra.
  unfold is_zero_poly in *. apply Forall_cons; [lra | exact H].
Qed.

Lemma degree_poly_sub_lt_diff_len : forall n l1 l2,
  (length l1 + length l2 <= n)%nat ->
  degree l1 = degree l2 -> lead_coeff l1 = lead_coeff l2 ->
  (degree (poly_sub l1 l2) < degree l1 \/ is_zero_poly (poly_sub l1 l2))%nat.
Proof.
  induction n as [| n IH].
  - intros l1 l2 H Hdeg Hlead. assert (l1 = []) by (destruct l1; simpl in *; auto; lia).
    assert (l2 = []) by (destruct l2; simpl in *; auto; lia). subst.
    right. unfold poly_sub, poly_add, poly_add_rev, poly_opp, rev; simpl. apply Forall_nil.
  - intros l1 l2 H Hdeg Hlead.
    destruct (Nat.compare (length l1) (length l2)) eqn:Heq.
    + apply Nat.compare_eq_iff in Heq. apply degree_poly_sub_eq_len; auto.
    + apply Nat.compare_lt_iff in Heq.
      destruct l2 as [| h2 t2]. simpl in Heq; lia.
      assert (Hh2 : h2 = 0).
      { destruct (Req_EM_T h2 0) as [|Hh2']; auto.
        pose proof (degree_le_length l1) as Hl1.
        destruct l1 as [| h1 t1].
        - simpl in Hlead. destruct (Req_EM_T h2 0) as [|Hh2'']. contradiction. lra.
        - simpl in *. destruct (Req_EM_T h2 0); [contradiction|]. destruct (Req_EM_T h1 0); lia. }
      subst.
      rewrite poly_sub_pad_r; try lia.
      destruct (IH l1 t2) as [Hlt | Hz].
      * simpl in H. lia.
      * simpl in Hdeg. destruct (Req_EM_T 0 0) as [_|HF]; [|lra]. exact Hdeg.
      * simpl in Hlead. destruct (Req_EM_T 0 0) as [_|HF]; [|lra]. exact Hlead.
      * left. rewrite degree_cons_neg_0. exact Hlt.
      * right. rewrite is_zero_poly_cons_neg_0. exact Hz.
      * simpl in *. lia.
    + apply Nat.compare_gt_iff in Heq.
      destruct l1 as [| h1 t1]. simpl in Heq; lia.
      assert (Hh1 : h1 = 0).
      { destruct (Req_EM_T h1 0) as [|Hh1']; auto.
        pose proof (degree_le_length l2) as Hl2.
        destruct l2 as [| h2 t2].
        - simpl in Hlead. destruct (Req_EM_T h1 0) as [|Hh1'']. contradiction. lra.
        - simpl in *. destruct (Req_EM_T h1 0); [contradiction|]. destruct (Req_EM_T h2 0); lia. }
      subst.
      rewrite poly_sub_pad_l; try lia.
      destruct (IH t1 l2) as [Hlt | Hz].
      * simpl in H. lia.
      * simpl in Hdeg. destruct (Req_EM_T 0 0) as [_|HF]; [|lra]. exact Hdeg.
      * simpl in Hlead. destruct (Req_EM_T 0 0) as [_|HF]; [|lra]. exact Hlead.
      * left. rewrite degree_cons_0. simpl. destruct (Req_dec_T 0 0); auto. lra.
      * right. rewrite is_zero_poly_cons_0. exact Hz.
      * simpl in *. lia.
Qed.

Lemma degree_poly_sub_lt : forall l1 l2,
  degree l1 = degree l2 ->
  lead_coeff l1 = lead_coeff l2 ->
  (degree (poly_sub l1 l2) < degree l1 \/ is_zero_poly (poly_sub l1 l2))%nat.
Proof.
  intros. apply degree_poly_sub_lt_diff_len with (n := (length l1 + length l2)%nat); auto.
Qed.

Lemma is_zero_poly_sub_zero : forall l1 l2,
  is_zero_poly l1 -> is_zero_poly l2 -> is_zero_poly (poly_sub l1 l2).
Proof.
  intros l1 l2 H1 H2; apply poly_equiv_iff_sub_zero; intros x; pose proof (is_zero_poly_eval _ x H1) as H3; pose proof (is_zero_poly_eval _ x H2) as H4; lra.
Qed.

Lemma is_zero_poly_scale_0 : forall l,
  is_zero_poly (poly_scale 0 l).
Proof.
  intros l; induction l as [| h t IH].
  - apply Forall_nil.
  - unfold poly_scale in *. simpl. apply Forall_cons; [lra | exact IH].
Qed.

Lemma poly_sub_cancel_lead : forall S B m,
  ~ is_zero_poly B ->
  degree S = degree B ->
  m = lead_coeff S / lead_coeff B ->
  (degree (poly_sub S (poly_scale m B)) < degree B \/ is_zero_poly (poly_sub S (poly_scale m B)))%nat.
Proof.
  intros S B m H1 H2 H3.
  assert (H4 : lead_coeff B <> 0).
  { intros H5. apply H1. apply lead_coeff_zero_iff. apply H5. }
  destruct (Req_EM_T m 0) as [H5 | H5].
  - assert (H6 : lead_coeff S = 0).
    { rewrite H3 in H5.  unfold Rdiv in H5.
      apply Rmult_integral in H5.
      destruct H5 as [H5 | H5].
      - exact H5.
      - pose proof (Rinv_neq_0_compat _ H4). lra. } 
    apply lead_coeff_zero_iff in H6.
    right. apply is_zero_poly_sub_zero.
    + apply H6.
    + rewrite H5. apply is_zero_poly_scale_0.
  - assert (H6 : degree (poly_scale m B) = degree B).
    { apply degree_poly_scale. apply H5. }
    assert (H7 : lead_coeff (poly_scale m B) = lead_coeff S).
    { rewrite lead_coeff_poly_scale. rewrite H3. unfold Rdiv.
      rewrite Rmult_comm. solve_R. }
    assert (H8 : degree S = degree (poly_scale m B)).
    { rewrite H2, H6. reflexivity. }
    pose proof degree_poly_sub_lt S (poly_scale m B) H8 as H9.
    assert (H10 : lead_coeff S = lead_coeff (poly_scale m B)) by lra.
    apply H9 in H10. rewrite H2 in H10. apply H10.
Qed.

Lemma poly_div_equal_degree : forall S B,
  ~ is_zero_poly B ->
  degree S = degree B ->
  exists m : R,
    (degree (poly_sub S (poly_scale m B)) < degree B \/ is_zero_poly (poly_sub S (poly_scale m B)))%nat.
Proof.
  intros S B H1 H2.
  exists (lead_coeff S / lead_coeff B).
  apply poly_sub_cancel_lead; auto.
Qed.

Lemma poly_div_step : forall R_poly B c,
  ~ is_zero_poly B ->
  (degree R_poly < degree B \/ is_zero_poly R_poly)%nat ->
  exists q r : list R,
    (forall x, x * polynomial R_poly x + c = polynomial B x * polynomial q x + polynomial r x) /\
    (degree r < degree B \/ is_zero_poly r)%nat.
Proof.
  intros R_poly B c HB HR.
  set (S := R_poly ++ [c]).
  assert (HS_eval : forall x, polynomial S x = x * polynomial R_poly x + c).
  { intros x. unfold S. apply poly_shift. }
  
  destruct (is_zero_poly_dec S) as [HzS | HnzS].
  - exists [], S.
    split.
    + intros x. rewrite HS_eval, poly_nil. lra.
    + right. apply HzS.
    
  - 
    assert (HdegS : (degree S <= degree B)%nat).
    { apply degree_shifted_le; auto. }
    
    destruct (Nat.eq_dec (degree S) (degree B)) as [Heq | Hneq].
    
    + 
      pose proof poly_div_equal_degree S B HB Heq as [m Hcancel].
      exists [m], (poly_sub S (poly_scale m B)).
      split.
      * intros x. rewrite <- HS_eval.
        rewrite eval_poly_sub, eval_poly_scale, poly_const_eval.
        lra.
      * apply Hcancel.
      
    + assert (Hlt : (degree S < degree B)%nat) by lia.
      exists [], S.
      split.
      * intros x. rewrite HS_eval, poly_nil. lra.
      * left. apply Hlt.
Qed.

Lemma poly_division_exists : forall A B : list R,
  ~ is_zero_poly B ->
  exists Q R_poly : list R,
    (forall x, polynomial A x = polynomial B x * polynomial Q x + polynomial R_poly x) /\
    (degree R_poly < degree B \/ is_zero_poly R_poly)%nat.
Proof.
  intros A B H1.
  induction A as [| c A' H2] using rev_ind.
  - exists [], []. split.
    + intros x. repeat rewrite poly_nil. lra.
    + right. apply Forall_nil.
  - destruct H2 as [Q' [R' [H3 H4]]].
    pose proof poly_div_step R' B c H1 H4 as [q [r [H5 H6]]].
    exists (poly_add (Q' ++ [0]) q), r.
    split; auto.
    intros x.
    rewrite poly_shift.
    rewrite H3.
    rewrite eval_poly_add.
    rewrite poly_shift.
    pose proof H5 x as H7.
    lra.
Qed.

Definition poly_coprime (A B : list R) : Prop :=
  exists U V : list R, forall x, 
    polynomial U x * polynomial A x + polynomial V x * polynomial B x = 1.

Lemma zero_poly_degree_0_val : forall l, is_zero_poly l -> degree l = 0%nat.
Proof.
  intros l Hl. induction l as [| h t IH].
  - reflexivity.
  - inversion Hl; subst. simpl. destruct (Req_EM_T 0%R 0%R).
    + apply IH; assumption.
    + lra.
Qed.

Lemma not_zero_poly_degree_gt_0 : forall l, (0 < degree l)%nat -> ~ is_zero_poly l.
Proof.
  intros l Hl Hz. apply zero_poly_degree_0_val in Hz. lia.
Qed.

Lemma degree_bound_from_div : forall R_poly B,
  (0 < degree B)%nat ->
  (degree R_poly < degree B \/ is_zero_poly R_poly)%nat ->
  (degree R_poly < degree B)%nat.
Proof.
  intros R_poly B HB Hdiv.
  destruct Hdiv as [Hlt | HZ].
  - exact Hlt.
  - apply zero_poly_degree_0_val in HZ. lia.
Qed.

Lemma sum_f_rev_index : forall n (f : nat -> R), sum_f 0 n f = sum_f 0 n (fun i => f (n - i)%nat).
Proof.
  intros n f. induction n as [|n IH].
  - rewrite sum_f_0_0, sum_f_0_0. replace (0 - 0)%nat with 0%nat by lia. reflexivity.
  - rewrite sum_f_i_Sn_f; try lia.
    rewrite sum_f_Si with (i := 0%nat) (f := fun i => f (S n - i)%nat); try lia.
    rewrite IH. f_equal. rewrite sum_f_reindex' with (s := 1%nat). 
    replace (0 + 1)%nat with 1%nat by lia. 
    replace (n + 1)%nat with (S n) by lia. 
    apply sum_f_equiv; try lia. 
    intros i Hi. f_equal. lia.
Qed.

Lemma sum_f_0_pow : forall n (f : nat -> R),
  sum_f 0 n (fun i => f i * 0 ^ (n - i)) = f n.
Proof.
  induction n as [| n IH].
  - intros f. rewrite sum_f_0_0. replace (0 - 0)%nat with 0%nat by lia.
    replace (0^0) with 1 by lra. lra.
  - intros f. rewrite sum_f_i_Sn_f; try lia.
    replace (S n - S n)%nat with 0%nat by lia.
    replace (0^0) with 1 by lra.
    assert (H_zero : sum_f 0 n (fun i : nat => f i * 0 ^ (S n - i)) = 0).
    {
      transitivity (sum_f 0 n (fun _ : nat => 0)).
      - apply sum_f_equiv; try lia. intros i Hi. 
        replace (S n - i)%nat with (S (n - i))%nat by lia.
        simpl. lra.
      - clear IH. induction n as [| n' IHn'].
        + rewrite sum_f_0_0. reflexivity.
        + rewrite sum_f_i_Sn_f; try lia. rewrite IHn'. lra.
    }
    rewrite H_zero. lra.
Qed.

Lemma poly_eval_0 : forall l, (length l > 0)%nat -> polynomial l 0 = nth (length l - 1) l 0.
Proof.
  intros l H.
  unfold polynomial.
  pose proof sum_f_0_pow (length l - 1) (fun i => nth i l 0) as H1.
  exact H1.
Qed.

Lemma rev_length_minus_1_nth : forall l (d : R),
  (length l > 0)%nat ->
  nth (length l - 1) (rev l) d = nth 0 l d.
Proof.
  intros l d H. rewrite rev_nth; try lia.
  replace (length l - S (length l - 1))%nat with 0%nat by lia. reflexivity.
Qed.

Lemma poly_rev_eval_eq : forall l x, x <> 0 ->
  (length l > 0)%nat ->
  polynomial (rev l) x = x ^ (length l - 1) * polynomial l (1/x).
Proof.
  intros l x Hx Hlen.
  unfold polynomial.
  rewrite length_rev.
  rewrite r_mult_sum_f_i_n_f_l.
  rewrite sum_f_rev_index.
  apply sum_f_equiv; try lia.
  intros i H.
  rewrite rev_nth; try lia.
  replace (length l - S (length l - 1 - i))%nat with i by lia.
  replace (length l - 1 - (length l - 1 - i))%nat with i by lia.
  replace (1 / x) with (/ x) by lra.
  first [ rewrite pow_inv; auto | rewrite pow_inv; auto ].
  replace (Datatypes.length l - 1)%nat with (i + (Datatypes.length l - 1 - i))%nat at 1 by lia.
  rewrite pow_add.
  field; auto; try apply pow_nonzero; auto.
Qed.

Lemma limit_poly_1_x : forall l, (length l > 0)%nat ->
  ⟦ lim 0 ⟧ (fun x => x ^ (length l - 1) * polynomial l (1/x)) = nth 0 l 0.
Proof.
  intros l Hlen.
  apply limit_eq with (f1 := polynomial (rev l)).
  - exists 1. split; [lra |]. intros x H. symmetry.
    assert (H1 : x <> 0) by solve_abs.
  unfold polynomial.
  rewrite length_rev.
  rewrite r_mult_sum_f_i_n_f_l.
  symmetry.
  rewrite sum_f_rev.
  symmetry.
  apply sum_f_equiv; try lia.
  intros i H2.
  rewrite rev_nth; try lia.
  replace (Datatypes.length l - 1 - (Datatypes.length l - 1 - i))%nat with i by lia.
  replace (1 / x) with (/ x) by lra.
  first [ rewrite pow_inv; auto | rewrite pow_inv; auto ].
  replace (Datatypes.length l - 1)%nat with (i + (Datatypes.length l - 1 - i))%nat at 1 by lia.
  rewrite pow_add.
  field_simplify; try apply pow_nonzero; auto.
  replace (length l - S (length l - 1 - i))%nat with i by lia. auto.
  - pose proof (continuous_polynomial (rev l) 0) as H1. 
    unfold continuous_at in H1.
    replace (nth 0 l 0) with (polynomial (rev l) 0).
  1: exact H1.
  unfold polynomial.
  rewrite length_rev.
  erewrite sum_single_index with (k := (length l - 1)%nat).
  + replace (length l - 1 - (length l - 1))%nat with 0%nat by lia.
    simpl. rewrite Rmult_1_r.
    rewrite rev_nth; try lia.
    replace (length l - S (length l - 1))%nat with 0%nat by lia.
    reflexivity.
  + lia.
  + intros j H2 H3.
    replace (length l - 1 - j)%nat with (S (length l - 1 - j - 1))%nat by lia.
    simpl. lra.
Qed.

Lemma poly_cons_0_eval : forall l x, polynomial (0 :: l) x = polynomial l x.
Proof.
  intros l x. rewrite poly_cons. simpl. 
  replace (length l) with (length l - 0)%nat by lia. 
  lra.
Qed.

Lemma limit_0_pow : forall k, (0 < k)%nat -> ⟦ lim 0 ⟧ (fun y => y ^ k) = 0.
Proof.
  induction k as [| k IH].
  - intros H; lia.
  - intros _. destruct (Nat.eq_dec k 0) as [H1 | H1].
    + subst k. simpl. replace (fun y => y * 1) with (fun y : R => y) by (extensionality y; lra).
      apply limit_id.
    + replace (S k) with (k + 1)%nat by lia. rewrite <- Nat.add_1_r.
      simpl. replace (fun y => y ^ (k + 1)) with (fun y => y * y ^ k). 
      2 : { extensionality y. replace (k + 1)%nat with (S k) by lia. rewrite tech_pow_Rmult. auto. }
      replace 0 with (0 * 0) at 2 by lra. apply limit_mult. apply limit_id. apply IH; lia.
Qed.

Lemma limit_poly_lead_coeff : forall l,
  ~ is_zero_poly l ->
  exists f, (forall x, x <> 0 -> f x = x ^ (degree l) * polynomial l (1/x)) /\
  ⟦ lim 0 ⟧ f = lead_coeff l.
Proof.
  induction l as [| h t IH].
  - intros H; exfalso; apply H; apply Forall_nil.
  - destruct (Req_EM_T h 0) as [Heq | Hneq].
    + subst h. intros Hnz.
      assert (Hnzt : ~ is_zero_poly t).
      { intros Ht. apply Hnz. apply Forall_cons; auto. }
      specialize (IH Hnzt) as [f [Hf Hlim]].
      exists f. split; auto.
      intros x Hx. rewrite Hf; auto.
      simpl. destruct (Req_EM_T 0 0); try lra.
      rewrite poly_cons_0_eval. reflexivity. simpl. destruct (Req_dec_T 0 0); [exact Hlim | lra].
    + intros Hnz.
      exists (fun x => x ^ (length (h::t) - 1) * polynomial (h::t) (1/x)).
      split.
      * intros x Hx. simpl. destruct (Req_EM_T h 0); try lra.
      * simpl. destruct (Req_EM_T h 0); try lra.
        replace (length t - 0)%nat with (length t)%nat by lia.
  apply limit_eq with (f1 := polynomial (rev (h :: t))).
  -- exists 1. split; [lra |].
    intros x Hx.
    assert (Hx0 : x <> 0) by solve_abs.
    unfold polynomial.
    rewrite length_rev.
    replace (length (h :: t) - 1)%nat with (length t)%nat by (simpl; lia).
    rewrite r_mult_sum_f_i_n_f_l.
    assert (sum_f_rev : forall n' f0, ∑ 0 n' f0 = ∑ 0 n' (fun i => f0 (n' - i)%nat)).
    {
      clear.
      induction n' as [| n' IH]; intros f0.
      - simpl. repeat rewrite sum_f_0_0; auto.
      - rewrite sum_f_i_Sn_f; try lia.
        rewrite IH.
        rewrite sum_f_Si with (i := 0%nat) (n := S n') (f := fun i => f0 (S n' - i)%nat); try lia.
        replace (f0 (S n' - 0)%nat) with (f0 (S n')) by (f_equal; lia).
        replace (∑ 0 n' (λ i : ℕ, f0 (n' - i)%nat) + f0 (S n')) with (f0 (S n') + ∑ 0 n' (λ i : ℕ, f0 (n' - i)%nat)) by lra.
        field_simplify.
        rewrite sum_f_reindex' with (s := 1%nat) (i := 0%nat) (n := n').
        replace (n' + 1)%nat with (S n') by lia.
        f_equal.
        apply sum_f_equiv; try lia.
        intros k Hk. f_equal. lia.
    }
    symmetry.
    rewrite sum_f_rev.
    symmetry.
    apply sum_f_equiv; try lia.
    intros i H2.
    rewrite rev_nth; try (simpl; lia).
    replace (length (h :: t) - 1 - i)%nat with (length t - i)%nat by (simpl; lia).
    replace (length t - (length t - i))%nat with i by lia.
    replace (1 / x) with (/ x) by lra.
    rewrite pow_inv; auto.
    replace (x ^ length t) with (x ^ (length t - i) * x ^ i).
    2: { rewrite <- pow_add. f_equal. lia. }
    replace (length (h :: t) - S i)%nat with (length t - i)%nat by (simpl; lia).
    field_simplify.
    ++ reflexivity.
    ++ apply pow_nonzero. exact Hx0.
  -- assert (Hh: polynomial (rev (h :: t)) 0 = h).
     {
       unfold polynomial.
       rewrite length_rev.
       replace (length (h :: t) - 1)%nat with (length t)%nat by (simpl; lia).
       erewrite sum_single_index with (k := (length t)%nat).
       * replace (length t - length t)%nat with 0%nat by lia.
         simpl. rewrite Rmult_1_r.
         rewrite app_nth2.
         ** rewrite length_rev. replace (length t - length t)%nat with 0%nat by lia. reflexivity.
         ** rewrite length_rev. lia.
       * lia.
       * intros j H2 H3.
         replace (length t - j)%nat with (S (length t - j - 1))%nat by lia.
         simpl. lra.
     }
     pose proof (continuous_polynomial (rev (h::t)) 0) as Hc.
     unfold continuous_at in Hc.
     replace (polynomial (rev (h :: t)) 0) with h in Hc; auto.
Qed.

Lemma limit_eq_zero_mult : forall f g a,
  ⟦ lim a ⟧ f = 0 ->
  (exists M δ, δ > 0 /\ forall x, 0 < |x - a| < δ -> |g x| <= M) ->
  ⟦ lim a ⟧ (fun x => f x * g x) = 0.
Proof.
  intros f g a H1 [M [δ1 [Hδ1 Hbd]]] ε Heps.
  assert (H_M : M + 1 > 0).
  { pose proof (Rtotal_order 0 M) as [H | [H | H]]. lra. lra. 
    specialize (Hbd (a + δ1 / 2) ltac:(solve_abs)). solve_abs. }
  specialize (H1 (ε / (M + 1)) ltac:(apply Rdiv_pos_pos; lra)) as [δ2 [Hδ2 Hf]].
  exists (Rmin δ1 δ2). split; [solve_min |].
  intros x Hx.
  specialize (Hbd x ltac:(solve_min)).
  specialize (Hf x ltac:(solve_min)).
  replace (f x * g x - 0) with (f x * g x) by lra.
  rewrite Rabs_mult.
  assert (|f x| < ε / (M + 1)) by solve_abs.
  assert (|g x| < M + 1) by lra.
  assert (|f x| * |g x| < (ε / (M + 1)) * (M + 1)).
  { apply Rmult_le_0_lt_compat; try solve_abs; nra. }
  replace (ε / (M + 1) * (M + 1)) with ε in H1 by (field; lra).
  exact H1.
Qed.

Lemma bounded_poly_1_x : forall l,
  exists M δ, δ > 0 /\ forall x, 0 < |x - 0| < δ -> |x ^ (degree l) * polynomial l (1/x)| <= M.
Proof.
  intros l.
  destruct (is_zero_poly_dec l) as [Hz | Hnz].
  - exists 0, 1. split; [lra |]. intros x Hx.
    pose proof (is_zero_poly_eval l (1/x) Hz) as Hval. rewrite Hval. solve_abs.
  - pose proof (limit_poly_lead_coeff l Hnz) as [f [Hf Hlim]].
    specialize (Hlim 1 ltac:(lra)) as [δ [Hδ Hfbd]].
    exists (|lead_coeff l| + 1), δ. split; [lra |].
    intros x Hx. specialize (Hfbd x Hx).
    rewrite <- Hf; try solve_abs.
Qed.

Lemma limit_pow_poly : forall k l,
  (degree l < k)%nat ->
  ⟦ lim 0 ⟧ (fun x => x ^ k * polynomial l (1/x)) = 0.
Proof.
  intros k l H.
  replace (fun x => x ^ k * polynomial l (1/x))
    with (fun x => (x ^ (k - degree l)) * (x ^ (degree l) * polynomial l (1/x))).
  2 : {
    extensionality x.
    destruct (Req_EM_T x 0) as [H1 | H1].
    - subst x. rewrite pow_ne_zero; try lia. replace (0 * _) with 0 by lra.
      rewrite pow_ne_zero; try lia. replace (0 * _) with 0 by lra. reflexivity.
    - rewrite <- Rmult_assoc. f_equal. rewrite <- pow_add. f_equal. lia.
  }
  apply limit_eq_zero_mult.
  - apply limit_0_pow. lia.
  - apply bounded_poly_1_x.
Qed.

Lemma limit_0_add : forall f1 f2 c1 c2,
  ⟦ lim 0 ⟧ f1 = c1 -> ⟦ lim 0 ⟧ f2 = c2 -> ⟦ lim 0 ⟧ (fun x => f1 x + f2 x) = c1 + c2.
Proof.
  intros. apply limit_plus; auto.
Qed.

Lemma limit_0_sub : forall f1 f2 c1 c2,
  ⟦ lim 0 ⟧ f1 = c1 -> ⟦ lim 0 ⟧ f2 = c2 -> ⟦ lim 0 ⟧ (fun x => f1 x - f2 x) = c1 - c2.
Proof.
  intros. apply limit_minus; auto.
Qed.

Lemma horizontal_split_degree_helper : forall P A B U V,
  (0 < degree A)%nat ->
  (0 < degree B)%nat ->
  (degree P < degree A + degree B)%nat ->
  (degree V < degree A)%nat ->
  (forall x, polynomial P x = polynomial U x * polynomial A x + polynomial V x * polynomial B x) ->
  (degree U < degree B)%nat.
Proof.
  intros P A B U V H_A_pos H_B_pos H_P_deg H_V_deg H_eq.
  destruct (is_zero_poly_dec U) as [H_U_zero | H_U_nZ].
  - apply zero_poly_degree_0_val in H_U_zero. rewrite H_U_zero. exact H_B_pos.
  - pose proof (limit_poly_lead_coeff U H_U_nZ) as [fU [HfU HdU]].
    destruct (is_zero_poly_dec A) as [H_A_zero | H_A_nZ].
    + apply zero_poly_degree_0_val in H_A_zero. lia.
    + pose proof (limit_poly_lead_coeff A H_A_nZ) as [fA [HfA HdA]].
      destruct (le_lt_dec (degree B) (degree U)) as [HdB_le_dU | H_U_deg_B_lt].
      2 : { exact H_U_deg_B_lt. }
      exfalso.
      
      set (k := (degree U + degree A)%nat).
      assert (Hk_gt_P : (degree P < k)%nat) by lia.
      assert (Hk_gt_V_B : (degree V + degree B < k)%nat) by lia.
      
      assert (H_P_lim : ⟦ lim 0 ⟧ (fun x : R => x ^ k * polynomial P (1 / x)) = 0).
      { apply limit_pow_poly. exact Hk_gt_P. }
      
      assert (H_VB_lim : ⟦ lim 0 ⟧ (fun x : R => x ^ k * (polynomial V (1 / x) * polynomial B (1 / x))) = 0).
      { 
        replace (fun x : R => x ^ k * (polynomial V (1 / x) * polynomial B (1 / x)))
          with (fun x : R => (x ^ (k - degree B) * polynomial V (1 / x)) * (x ^ degree B * polynomial B (1 / x))).
        2 : {
          extensionality x.
          destruct (Req_EM_T x 0) as [H1 | H1].
          - subst x.
            destruct (k - degree B)%nat as [| n_diff] eqn:Eq_diff. { lia. }
            destruct k as [| k'] eqn:Eq_k. { lia. }
            simpl. lra.
          - replace (x ^ (k - degree B) * polynomial V (1 / x) * (x ^ degree B * polynomial B (1 / x)))
              with (x ^ (k - degree B) * x ^ degree B * (polynomial V (1 / x) * polynomial B (1 / x))) by lra.
            rewrite <- pow_add. f_equal. unfold k. replace (degree U + degree A - degree B + degree B)%nat with (degree U + degree A)%nat by lia.
            auto.
        }
        apply limit_eq_zero_mult.
        - apply limit_pow_poly. lia.
        - apply bounded_poly_1_x.
      }
      
      assert (H_eq2 : forall x : R, x <> 0 ->
        x ^ k * polynomial U (1/x) * polynomial A (1/x) =
        x ^ k * polynomial P (1/x) - x ^ k * (polynomial V (1/x) * polynomial B (1/x))).
      { intros x Hx. pose proof (H_eq (1/x)) as H2. rewrite H2. lra. }
      
      assert (H_UA_lim : ⟦ lim 0 ⟧ (fun x : R => x ^ k * polynomial U (1/x) * polynomial A (1/x)) = 0).
      {
        apply limit_eq with (f1 := fun x : R => x ^ k * polynomial P (1/x) - x ^ k * (polynomial V (1/x) * polynomial B (1/x))).
        - exists 1. split; [lra |]. intros x Hx. symmetry. apply H_eq2. solve_abs.
        - replace 0 with (0 - 0) at 2 by lra. apply limit_minus; auto.
      }
      
      assert (H_UA_lim2 : ⟦ lim 0 ⟧ (fun x : R => fU x * fA x) = lead_coeff U * lead_coeff A).
      { apply limit_mult; auto. }
      
      assert (H_UA_lim3 : ⟦ lim 0 ⟧ (fun x : R => fU x * fA x) = 0).
      {
        apply limit_eq with (f1 := fun x : R => x ^ k * polynomial U (1/x) * polynomial A (1/x)).
        - exists 1. split; [lra |]. intros x Hx.
          rewrite HfU; try solve_abs; rewrite HfA; try solve_abs.
          unfold k. rewrite pow_add; lra. unfold k.
          rewrite pow_add. lra.
        - exact H_UA_lim.
      }
      
      pose proof (limit_unique _ 0 _ _ H_UA_lim2 H_UA_lim3) as H_prod_0.
      apply Rmult_integral in H_prod_0.
      destruct H_prod_0 as [H_zero | H_zero].
      * apply lead_coeff_zero_iff in H_zero. contradiction.
      * apply lead_coeff_zero_iff in H_zero. contradiction.
Qed.


Lemma fraction_eq_helper : forall p u a v b : R,
  p = u * a + v * b ->
  a * b <> 0 ->
  p / (a * b) = u / b + v / a.
Proof.
  intros p u a v b H H0.
  assert (Ha : a <> 0). { intro H1. apply H0. rewrite H1. lra. }
  assert (Hb : b <> 0). { intro H1. apply H0. rewrite H1. lra. }
  rewrite H. unfold Rdiv.
  rewrite Rinv_mult; auto.
  replace ((u * a + v * b) * (/ a * / b)) with (u * (/ b) * (a * / a) + v * (/ a) * (b * / b)) by lra.
  rewrite (Rinv_r a Ha).
  rewrite (Rinv_r b Hb).
  lra.
Qed.

Lemma horizontal_split : forall P A B : list R,
  poly_coprime A B ->
  (0 < degree A)%nat ->
  (0 < degree B)%nat ->
  (degree P < degree A + degree B)%nat ->
  exists U V : list R,
    (degree U < degree B)%nat /\ (degree V < degree A)%nat /\
    (forall x, polynomial P x = polynomial U x * polynomial A x + polynomial V x * polynomial B x) /\
    (forall x, polynomial A x * polynomial B x <> 0 ->
      polynomial P x / (polynomial A x * polynomial B x) = 
      polynomial U x / polynomial B x + polynomial V x / polynomial A x).
Proof.
  intros P A B [U0 [V0 Hcop]] HdegA HdegB HdegP.
  
  pose proof (not_zero_poly_degree_gt_0 A HdegA) as HnzA.
  pose proof (poly_division_exists (poly_mul P V0) A HnzA) as [Q [V [Hdiv HdegV_raw]]].
  set (U := poly_add (poly_mul P U0) (poly_mul Q B)).
  exists U, V.
  
  assert (Hpoly : forall x, polynomial P x = polynomial U x * polynomial A x + polynomial V x * polynomial B x).
  {
    intro x.
    unfold U.
    rewrite eval_poly_add.
    repeat rewrite eval_poly_mul.
    pose proof (Hcop x) as H1.
    pose proof (Hdiv x) as H2.
    rewrite eval_poly_mul in H2.
    assert (Hv : polynomial V x = polynomial P x * polynomial V0 x - polynomial A x * polynomial Q x) by lra.
    rewrite Hv.
    replace ((polynomial P x * polynomial U0 x + polynomial Q x * polynomial B x) * polynomial A x + (polynomial P x * polynomial V0 x - polynomial A x * polynomial Q x) * polynomial B x)
       with (polynomial P x * (polynomial U0 x * polynomial A x + polynomial V0 x * polynomial B x)) by ring.
    rewrite H1.
    ring.
  }
  
  assert (HV_bound : (degree V < degree A)%nat).
  { apply degree_bound_from_div; auto. }
  
  assert (HU_bound : (degree U < degree B)%nat).
  { apply horizontal_split_degree_helper with (P := P) (A := A) (B := B) (U := U) (V := V); auto. }
  
  split; [exact HU_bound |].
  split; [exact HV_bound |].
  split; [exact Hpoly |].
  
  intros x Hnz.
  apply fraction_eq_helper.
  - exact (Hpoly x).
  - exact Hnz.
Qed.

Lemma bezout_identity : forall A B : list R,
  poly_coprime A B ->
  (0 < degree A)%nat ->
  (0 < degree B)%nat ->
  exists U V : list R, 
    (degree U < degree B)%nat /\ (degree V < degree A)%nat /\
    forall x, polynomial U x * polynomial A x + polynomial V x * polynomial B x = 1.
Proof.
  intros A B Hcop HA HB.
  
  (* The degree of the constant polynomial [1] cleanly evaluates to 0, 
     which is strictly less than the positive degree sums of A and B. *)
  assert (Hdeg: (degree [1%R] < degree A + degree B)%nat).
  { 
    simpl. destruct (Req_EM_T 1%R 0%R).
    - lra.
    - lia. 
  }
  
  (* Instantiate the universally continuous horizontal_split onto P = [1] *)
  pose proof (horizontal_split [1%R] A B Hcop HA HB Hdeg) as [U [V [HU [HV [Hpoly _]]]]].
  
  exists U, V.
  split; [exact HU |].
  split; [exact HV |].
  
  intro x.
  (* Extract the exact algebraic equality for the constant polynomial 1 *)
  pose proof (Hpoly x) as Hx.
  rewrite poly_const_eval in Hx.
  symmetry. 
  exact Hx.
Qed.

Lemma vertical_split : forall (P A : list R) (n : nat),
  (degree P < n * degree A)%nat ->
  exists C : nat -> list R,
    (forall i, (1 <= i <= n)%nat -> (degree (C i) < degree A)%nat) /\
    forall x, polynomial A x <> 0 ->
      polynomial P x / (polynomial A x ^ n) = 
      ∑ 1 n (λ i, polynomial (C i) x / polynomial A x ^ i).
Proof.
  intros P A n. generalize dependent P. induction n as [| n IH].
  - intros P H_P_deg.
    simpl in H_P_deg. lia.
  - intros P H_P_deg.
    assert (H_A_pos : (0 < degree A)%nat).
    { destruct (degree A) eqn:Hdeg; lia. }
    destruct (le_lt_dec (S n) 1) as [H_n_1 | H_n_gt_1].
    + assert (n = 0)%nat by lia. subst n.
      assert (HnzA : ~ is_zero_poly A) by (apply not_zero_poly_degree_gt_0; lia).
      pose proof (poly_division_exists P A HnzA) as [Q [R_poly [H_div H_deg]]].
      exists (fun i => if Nat.eq_dec i 1 then P else []).
      split.
      * intros i H_i. assert (i = 1)%nat by lia. subst i. destruct (Nat.eq_dec 1 1).
        ** replace (1 * degree A)%nat with (degree A) in H_P_deg by lia. exact H_P_deg.
        ** contradiction.
      * intros x H_A_nz.
        rewrite sum_f_n_n.
        destruct (Nat.eq_dec 1 1).
        ** simpl. rewrite Rmult_1_r. reflexivity.
        ** contradiction.
    + assert (n > 0)%nat by lia.
      assert (HnzA : ~ is_zero_poly A) by (apply not_zero_poly_degree_gt_0; lia).
      pose proof (poly_division_exists P A HnzA) as [Q [R_poly [H_div H_deg]]].
      assert (H_Q_deg : (degree Q < n * degree A)%nat).
      {
        destruct (is_zero_poly_dec Q) as [H_Q_zero | H_Q_nZ].
        { apply zero_poly_degree_0_val in H_Q_zero. rewrite H_Q_zero. apply Nat.mul_pos_pos; lia. }
        {
          pose proof (limit_poly_lead_coeff Q H_Q_nZ) as [fQ [HfQ HdQ]].
          pose proof (limit_poly_lead_coeff A HnzA) as [fA [HfA HdA]].
          destruct (le_lt_dec (n * degree A) (degree Q)) as [HdB_le_dU | H_Q_deg_A_lt].
          2 : { exact H_Q_deg_A_lt. }
          exfalso.
          set (k := (degree Q + degree A)%nat).
          assert (Hk_gt_P : (degree P < k)%nat) by lia.
          assert (Hk_gt_R : (degree R_poly < k)%nat).
          { destruct H_deg; [lia | apply zero_poly_degree_0_val in H0; lia]. }
          
          assert (H_P_lim : ⟦ lim 0 ⟧ (fun x : R => x ^ k * polynomial P (1 / x)) = 0).
          { apply limit_pow_poly. exact Hk_gt_P. }
          
          assert (H_R_lim : ⟦ lim 0 ⟧ (fun x : R => x ^ k * polynomial R_poly (1 / x)) = 0).
          { apply limit_pow_poly. exact Hk_gt_R. }
          
          assert (H_eq2 : forall x : R, x <> 0 ->
            x ^ k * polynomial Q (1/x) * polynomial A (1/x) =
            x ^ k * polynomial P (1/x) - x ^ k * polynomial R_poly (1/x)).
          { intros x Hx. pose proof (H_div (1/x)) as H2. rewrite H2. lra. }
          
          assert (H_QA_lim : ⟦ lim 0 ⟧ (fun x : R => x ^ k * polynomial Q (1/x) * polynomial A (1/x)) = 0).
          {
            apply limit_eq with (f1 := fun x : R => x ^ k * polynomial P (1/x) - x ^ k * polynomial R_poly (1/x)).
            exists 1. split; [lra |]. intros x Hx. symmetry. apply H_eq2. solve_abs.
            replace 0 with (0 - 0) at 2 by lra. apply limit_minus; auto.
          }
          
          assert (H_QA_lim2 : ⟦ lim 0 ⟧ (fun x : R => fQ x * fA x) = lead_coeff Q * lead_coeff A).
          { apply limit_mult; auto. }
          
          assert (H_QA_lim3 : ⟦ lim 0 ⟧ (fun x : R => fQ x * fA x) = 0).
          {
            apply limit_eq with (f1 := fun x : R => x ^ k * polynomial Q (1/x) * polynomial A (1/x)).
            exists 1. split; [lra |]. intros x Hx.
            rewrite HfQ; try solve_abs; rewrite HfA; try solve_abs.
            replace k with (degree Q + degree A)%nat by reflexivity.
            rewrite pow_add. lra. unfold k. rewrite pow_add. lra.
            exact H_QA_lim.
          }
          
          pose proof (limit_unique _ 0 _ _ H_QA_lim2 H_QA_lim3) as H_prod_0.
          apply Rmult_integral in H_prod_0.
          destruct H_prod_0 as [H_zero | H_zero].
          { apply lead_coeff_zero_iff in H_zero. contradiction. }
          { apply lead_coeff_zero_iff in H_zero. contradiction. }
        }
      }
      specialize (IH Q H_Q_deg) as [C' [H_C'_deg H_C'_eq]].
      exists (fun i => if Nat.eq_dec i (S n) then R_poly else C' i).
      split.
      * intros i H_i. destruct (Nat.eq_dec i (S n)) as [H_eq_Sn | H_neq_Sn].
        -- subst i. destruct H_deg as [H_lt | H_zero].
           ++ exact H_lt.
           ++ apply zero_poly_degree_0_val in H_zero. rewrite H_zero. exact H_A_pos.
        -- apply H_C'_deg. lia.
      * intros x H_A_nz.
        rewrite sum_f_i_Sn_f; try lia.
        destruct (Nat.eq_dec (S n) (S n)) as [H_eq_Sn | H_neq_Sn]; [| contradiction].
        assert (H_sum_C' : ∑ 1 n (λ i : nat, polynomial (if Nat.eq_dec i (S n) then R_poly else C' i) x / polynomial A x ^ i) = ∑ 1 n (λ i : nat, polynomial (C' i) x / polynomial A x ^ i)).
        { apply sum_f_equiv; try lia. intros k' H_k'. destruct (Nat.eq_dec k' (S n)); [lia | reflexivity]. }
        rewrite H_sum_C'.
        rewrite <- H_C'_eq; auto.
        pose proof (H_div x) as H_Px.
        rewrite H_Px.
        unfold Rdiv.
        rewrite Rmult_plus_distr_r.
        f_equal.
        replace (polynomial A x ^ S n) with (polynomial A x * polynomial A x ^ n) by (simpl; reflexivity).
        rewrite Rinv_mult; auto.
        replace (polynomial A x * polynomial Q x * (/ polynomial A x * / polynomial A x ^ n)) with (polynomial Q x * (/ polynomial A x ^ n) * (polynomial A x * / polynomial A x)) by lra.
        rewrite Rinv_r; auto; lra.
Qed.

Lemma partial_fraction_decomposition : forall (k l : nat)
  (α : nat -> R) (r : nat -> nat)
  (β γ : nat -> R) (s : nat -> nat)
  (p q : list R),
  (forall i, (1 <= i <= l)%nat -> (β i)^2 - 4 * γ i < 0) ->
  (degree p < degree q)%nat ->
  (forall x, polynomial q x = 
    (∏ 1 k (λ i, (x - α i)^(r i))) * (∏ 1 l (λ i, (x^2 + β i * x + γ i)^(s i)))) ->
  exists (A B C : nat -> nat -> R),
    forall x, polynomial q x <> 0 ->
      (polynomial p x) / (polynomial q x) = 
        ∑ 1 k (λ i, ∑ 1 (r i) (λ j, A i j / (x - α i)^j)) +
        ∑ 1 l (λ i, ∑ 1 (s i) (λ j, (B i j * x + C i j) / (x^2 + β i * x + γ i)^j)).
Proof.
  intros k l α r β γ s p q H1 H2 H3.
  revert p q H2 H3.
  induction k as [|k IHk].
  - induction l as [|l IHl].
    + intros p q H2 H3.
      exists (fun _ _ => 0), (fun _ _ => 0), (fun _ _ => 0).
      intros x H4.
      admit.
    + intros p q H2 H3.
      admit.
  - intros p q H2 H3.
    admit.
Admitted.

Lemma polynomial_inf_differentiable : forall l,
  let p := polynomial l in
  inf_differentiable p.
Proof.
  intros l p. induction l as [| h t IH].
  - unfold p. replace (polynomial []) with (fun _ : R => 0).
    2 : { extensionality x. rewrite poly_nil. reflexivity. }
    assert (H1 : forall n, ⟦ der^n ⟧ (fun _ : R => 0) = fun _ : R => 0).
    {
      intro n. induction n as [| k IH]; try reflexivity.
      exists (fun _ : R => 0). split; auto. apply derivative_const.
    }
    intro n. exists (fun _ : R => 0). auto.
  - unfold p. replace (polynomial _) with (fun x : R => h * x ^ length t + polynomial t x).
    2 : { extensionality x. rewrite poly_cons. reflexivity. }
    unfold inf_differentiable. intro n.
    destruct (IH n) as [gn' H1].
    destruct (le_gt_dec n (length t)) as [H2 | H2].
    + pose proof (nth_derivative_pow (length t) n H2) as H3.
      pose proof (nth_derivative_mult_const_l n h _ _ H3) as H4.
      eexists. apply nth_derivative_plus; eauto.
    + pose proof (nth_derivative_pow_gt n (length t) H2) as H3.
      pose proof (nth_derivative_mult_const_l n h _ _ H3) as H4.
      eexists. apply nth_derivative_plus; eauto.
Qed.

Lemma polynomial_derive_gt_degree : forall l n, (n > degree l)%nat -> forall x, ⟦ Der^n x ⟧ (polynomial l) = 0.
Proof.
  intros l n H1 x.
  pose proof (polynomial_inf_differentiable l n) as [gn' H2].
  assert (H3 : gn' = fun _ : R => 0).
  {
    generalize dependent gn'. generalize dependent n. induction l as [| h t H4].
    - intros n H5 gn' H6. replace (polynomial []) with (fun _ : R => 0) in H6.
      2 : { extensionality y. rewrite poly_nil. reflexivity. }
      assert (H7 : forall k, ⟦ der^k ⟧ (fun _ : R => 0) = fun _ : R => 0).
      { clear. intro k. induction k as [| m H8]; try reflexivity.
        unfold nth_derivative. fold nth_derivative.
        exists (fun _ : R => 0). split. exact H8. apply derivative_const. }
      pose proof (nth_derivative_unique n (fun _ : R => 0) gn' (fun _ : R => 0) H6 (H7 n)) as H9.
      exact H9.
    - intros n H5 gn' H6.
      simpl in H5. destruct (Req_dec_T h 0) as [H7 | H8].
      + subst h. replace (polynomial (0 :: t)) with (fun y : R => polynomial t y) in H6.
        2 : { extensionality y. rewrite poly_cons. lra. }
        apply (H4 n H5 gn' H6).
      + replace (polynomial _) with (fun y : R => h * y ^ length t + polynomial t y) in H6.
        2 : { extensionality y. rewrite poly_cons. reflexivity. }
        assert (H9 : (n > length t)%nat).
        { assert (length (h :: t) = S (length t)) by reflexivity. lia. }
        pose proof (nth_derivative_pow_gt n (length t) H9) as H10.
        pose proof (nth_derivative_mult_const_l n h _ _ H10) as H11.
        pose proof (polynomial_inf_differentiable t n) as [H12 H13].
        pose proof (nth_derivative_plus _ _ _ _ _ H11 H13) as H14.
        assert (H15 : H12 = fun _ : R => 0).
        { apply (H4 n); eauto. pose proof (degree_le_length t). lia. }
        rewrite H15 in H14.
        assert (H16 : (fun x0 : ℝ => h * (λ _ : ℝ, 0) x0 + (λ _ : ℝ, 0) x0) = fun _ : R => 0).
        { extensionality z. lra. }
        pose proof (nth_derivative_unique n (fun y : R => h * y ^ length t + polynomial t y) gn' _ H6 H14) as H17.
        rewrite H17. exact H16.
  }
  rewrite H3 in H2. apply nth_derivative_imp_nth_derive in H2.
  pose proof (f_equal (fun f => f x) H2) as H4. exact H4.
Qed.