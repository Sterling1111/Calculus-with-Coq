From Lib Require Import Imports Reals_util Sums Continuity Limit Notations Products.
Import LimitNotations SumNotations ProductNotations.

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
  - simpl. unfold poly_scale in *. simpl. destruct (Req_EM_T (m * h) 0) as [H1 | H1]; destruct (Req_EM_T h 0) as [H2 | H2].
    + assumption.
    + nra.
    + nra.
    + induction t; [reflexivity | simpl; repeat f_equal; auto]. admit.
Admitted.

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
    + subst. pose proof (degree_le_length t1). admit.
    + subst. pose proof (degree_le_length t2). admit.
    + replace (h1 - h2) with 0 by lra.
      destruct (is_zero_poly_dec (poly_sub t1 t2)) as [Hz | Hnz].
      * right. apply Forall_cons; auto.
      * left. rewrite degree_cons_0. pose proof (degree_le_length (poly_sub t1 t2)).
        rewrite poly_sub_length_eq in H; auto. admit.
Admitted.

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
      { destruct (Req_EM_T h2 0); auto.
        simpl in Hdeg. rewrite Hdeg in Hdeg.
        pose proof (degree_le_length l1). simpl in *. admit. }
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
      { destruct (Req_EM_T h1 0); auto.
        simpl in Hdeg. rewrite Hdeg in Hdeg.
        pose proof (degree_le_length l2). simpl in *. admit. }
      subst.
      rewrite poly_sub_pad_l; try lia.
      destruct (IH t1 l2) as [Hlt | Hz].
      * simpl in H. lia.
      * simpl in Hdeg. destruct (Req_EM_T 0 0) as [_|HF]; [|lra]. exact Hdeg.
      * simpl in Hlead. destruct (Req_EM_T 0 0) as [_|HF]; [|lra]. exact Hlead.
      * left. rewrite degree_cons_0. simpl. destruct (Req_dec_T 0 0); auto. lra.
      * right. rewrite is_zero_poly_cons_0. exact Hz.
Admitted.

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

Lemma bezout_identity : forall A B : list R,
  poly_coprime A B ->
  exists U V : list R, 
    (degree U < degree B)%nat /\ (degree V < degree A)%nat /\
    forall x, polynomial U x * polynomial A x + polynomial V x * polynomial B x = 1.
Proof. Admitted.

Lemma horizontal_split : forall P A B : list R,
  poly_coprime A B ->
  (degree P < degree A + degree B)%nat ->
  exists U V : list R,
    (degree U < degree B)%nat /\ (degree V < degree A)%nat /\
    forall x, polynomial A x * polynomial B x <> 0 ->
      polynomial P x / (polynomial A x * polynomial B x) = 
      polynomial U x / polynomial B x + polynomial V x / polynomial A x.
Proof. Admitted.

Lemma vertical_split : forall (P A : list R) (n : nat),
  (degree P < n * degree A)%nat ->
  exists C : nat -> list R,
    (forall i, (1 <= i <= n)%nat -> (degree (C i) < degree A)%nat) /\
    forall x, polynomial A x <> 0 ->
      polynomial P x / (polynomial A x ^ n) = 
      ∑ 1 n (λ i, polynomial (C i) x / polynomial A x ^ i).
Proof. Admitted.

Lemma partial_fraction_decomposition : forall (k l : nat)
  (α : nat -> R) (r : nat -> nat)
  (β γ : nat -> R) (s : nat -> nat)
  (p q : list R),
  (forall i, (1 <= i <= l)%nat -> (β i)^2 - 4 * γ i < 0) ->
  (length p <= length q)%nat ->
  (forall x, polynomial q x = 
    (∏ 1 k (λ i, (x - α i)^(r i))) * (∏ 1 l (λ i, (x^2 + β i * x + γ i)^(s i)))) ->
  exists (A B C : nat -> nat -> R),
    forall x, polynomial q x <> 0 ->
      (polynomial p x) / (polynomial q x) = 
        ∑ 1 k (λ i, ∑ 1 (r i) (λ j, A i j / (x - α i)^j)) +
        ∑ 1 l (λ i, ∑ 1 (s i) (λ j, (B i j * x + C i j) / (x^2 + β i * x + γ i)^j)).
Proof.
Admitted.