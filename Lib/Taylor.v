From Lib Require Import Imports Notations Reals_util Functions Sums Sets Exponential
                        Limit Continuity Derivative Trigonometry Interval Binomial Polynomial.
Import FunctionNotations SumNotations LimitNotations DerivativeNotations SetNotations IntervalNotations.

Open Scope R_scope.

Local Notation length := List.length.

Definition Taylor_polynomial (n : nat) (f : R -> R) (a : R) (x : R) : R :=
  ∑ 0 n (fun k => ((⟦ Der ^ k a ⟧ f) / (k!)) * ((x - a) ^ k)).

Notation "'P(' n ',' a ',' f ')'" := (Taylor_polynomial n f a) 
  (at level 10, n, a, f at level 9, format "P( n , a , f )").

Definition Taylor_remainder (n : nat) (f : R -> R) (a : R) (x : R) : R :=
  f x - P(n, a, f) x.

Notation "'R(' n ',' a ',' f ')'" := (Taylor_remainder n f a) 
  (at level 10, n, a, f at level 9, format "R( n , a , f )").

Lemma nth_derive_taylor_poly_const : forall n a f,
  ⟦ Der ^ n ⟧ (P(n, a, f)) = (fun _ => ⟦ Der ^ n a ⟧ f).
Proof.
  intros n a f. extensionality x. unfold Taylor_polynomial.
  rewrite nth_derive_sum; try lia.
  2: {
    intros k. destruct (lt_dec k n) as [H1 | H1].
    - apply nth_derivative_imp_nth_differentiable with (fn := λ _, ⟦ Der^k a ⟧ f / k! * 0).
      apply nth_derivative_mult_const_l. apply nth_derivative_pow_shift_gt; lia.
    - apply nth_derivative_imp_nth_differentiable with (fn := λ x, (⟦ Der^k a ⟧ f / k!) * (k! / (k - n)! * (x - a) ^ (k - n))).
      apply nth_derivative_mult_const_l. apply nth_derivative_pow_shift; lia.
  }
  destruct n.
  - simpl. rewrite sum_f_n_n. simpl. lra.
  - rewrite sum_f_i_Sn_f; try lia. rewrite Rplus_comm.
    replace (∑ 0 n (λ k : ℕ, (⟦ Der ^ (S n) ⟧ (λ x0 : ℝ, ⟦ Der ^ k a ⟧ f / k! * (x0 - a) ^ k)) x)) with 0.
    2: {
      rewrite sum_f_0; try lia; try lra. intros k H1.
      rewrite nth_derivative_imp_nth_derive with (f' := λ _, (⟦ Der^k a ⟧ f / k!) * 0); try lra.
      apply nth_derivative_mult_const_l. apply nth_derivative_pow_shift_gt; lia.
    }
    rewrite Rplus_0_r.
    rewrite nth_derivative_imp_nth_derive with (f' := λ _, (⟦ Der^(S n) a ⟧ f / (S n)!) * (S n)!); try lra.
    + field. apply INR_fact_neq_0.
    + apply nth_derivative_mult_const_l.
      replace (λ _ : ℝ, INR (fact (S n))) with (λ x : ℝ, INR (fact (S n)) / INR (fact (S n - S n)) * (x - a) ^ (S n - S n)).
      2 : { extensionality t. rewrite Nat.sub_diag, fact_0, pow_O, Rdiv_1_r. lra. }
      apply nth_derivative_pow_shift; lia.
Qed.

Lemma nth_derive_taylor_poly_at_const : forall n a f,
  ⟦ Der ^ n a ⟧ (P(n, a, f)) = ⟦ Der ^ n a ⟧ f.
Proof.
  intros n a f.
  rewrite nth_derive_taylor_poly_const.
  reflexivity.
Qed.

Lemma nth_derive_taylor_poly_eq : forall n k a f,
  (k <= n)%nat ->
  ⟦ Der ^ k a ⟧ (P(n, a, f)) = ⟦ Der ^ k a ⟧ f.
Proof.
  intros n k a f H1.
  unfold Taylor_polynomial.
  rewrite nth_derive_sum; try lia.
  2: { intros i. apply nth_differentiable_mult_const_l. apply nth_differentiable_pow_shift. }
  rewrite sum_single_index with (k := k); try lia.
  - rewrite nth_derive_mult_const_l; [|apply nth_differentiable_pow_shift].
    rewrite nth_derive_pow_shift; try lia. replace (k - k)%nat with 0%nat by lia. rewrite pow_O, Rmult_1_r, fact_0, Rdiv_1_r.
     field. apply INR_fact_neq_0.
  - intros j H2 H3.
    rewrite nth_derive_mult_const_l; [|apply nth_differentiable_pow_shift].
    assert ((j < k)%nat \/ (j > k)%nat) as [H4 | H4] by lia.
    + rewrite nth_derive_pow_shift_gt; try lia; try lra.
    + rewrite nth_derive_pow_shift; try lia.
      rewrite Rminus_diag. rewrite pow_i; try lia. lra.
Qed.

Lemma derive_at_f_minus_Q_zero : forall n a f,
  (n > 1)%nat ->
  differentiable_at f a ->
  let Q := P(n - 1, a, f) in
  ⟦ Der a ⟧ (f - Q) = 0.
Proof.
  intros n a f H1 H2 Q.
  rewrite derive_at_minus; auto.
  2: { 
    unfold Q, Taylor_polynomial. apply differentiable_at_sum; try lia.
    intros k H3. apply differentiable_at_mult_const_l, differentiable_at_pow_shift.
  }
  unfold Q, Taylor_polynomial.
  rewrite derive_at_sum; try lia. 
  2: { intros k H3. apply differentiable_at_mult_const_l, differentiable_at_pow_shift. }
  rewrite sum_single_index with (k := 1%nat); try lia.
  - rewrite derive_at_mult_const_l; [|apply differentiable_at_pow_shift].
    rewrite fact_1, Rdiv_1_r. replace (λ x : ℝ, (x - a) ^ 1) with (λ x : ℝ, x - a) by (extensionality x; lra).
    rewrite derive_at_minus; try apply differentiable_at_id; try apply differentiable_at_const.
    replace (⟦ Der^1 a ⟧ f) with (⟦ Der a ⟧ f) by auto.
    rewrite derive_at_id, derive_at_const; try lra.
  - intros j H3 H4.
    rewrite derive_at_mult_const_l; [|apply differentiable_at_pow_shift].
    assert (j = 0 \/ j > 1)%nat as [H5 | H5] by lia.
    + subst. simpl. rewrite derive_at_const. lra.
    + rewrite derive_at_pow_shift_zero; try lia. lra.
Qed.

Theorem theorem_20_1 : forall n a f,
  (n > 0)%nat -> 
  nth_differentiable_at n f a -> 
  ⟦ lim a ⟧ (λ x, (f x - P(n, a, f) x) / ((x - a)^n)) = 0.
Proof.
  intros n a f H1 H2.
  assert ((n = 1)%nat \/ (n > 1)%nat) as [H3 | H3] by lia; subst.
  - clear H1. rename H2 into H1. unfold Taylor_polynomial.
    apply limit_eq with (f1 := fun x => (f x - f a)/(x - a) - ⟦ Der a ⟧ f).
    {
      exists 1. split; try lra. intros x H4. rewrite sum_f_i_Sn_f; try lia. rewrite sum_f_n_n; try lia.
      replace ((⟦ Der^1 a ⟧ f)) with (⟦ Der a ⟧ f) by auto. solve_R.
    }
    assert (H2 : differentiable_at f a).
    { apply nth_differentiable_at_imp_differentiable_at with (n := 1%nat); auto. }
    assert (exists f', ⟦ der a ⟧ f = f') as [f' H3].
    { apply  differentiable_at_imp_derivative_at; auto. }
    pose proof derive_at_spec f f' a H2 as H4. apply H4 in H3 as H5.
    unfold derivative_at in H3. rewrite H5.
    replace 0 with (f' a - f' a) by lra.
    apply limit_minus_const.
    replace a with (0 + a) at 1 by lra.
    rewrite <- limit_shift with (a := 0)(c := a).
    replace (λ x, (f (x + a) - f a) / ((x + a) - a)) with (λ x, (f (a + x) - f a) / x); auto.
    extensionality x. replace ((x + a) - a) with x by lra. rewrite Rplus_comm. reflexivity.
  - pose proof (nth_differentiable_at_imp_neighborhood (n-1)%nat f a ltac:(replace (S (n - 1)) with n by lia; auto)) as [δ [H4 H5]].

    set (Q := P(n - 1, a, f)).
    set (C := ⟦ Der ^ n a ⟧ f / n!).
    set (g := λ x, (x - a)^n).

    apply limit_eq with (f1 := fun x => (f x - Q x)/((x - a)^n) - C).
    {
      exists δ. split; try lra. intros x H6.
      unfold Q, C, Taylor_polynomial. replace n with (S (n - 1))%nat at 5 by lia.
      rewrite sum_f_i_Sn_f; try lia. replace (S (n - 1)) with n by lia. field. split.
      - apply INR_fact_neq_0.
      - apply pow_nonzero. solve_R. 
    }
    replace 0 with (C - C) by lra.
    apply limit_minus_const.
    apply lhopital_nth_neighborhood with (n := (n-1)%nat).
    + exists δ. split; auto. 
      destruct H5 as [fn H5].
      assert (nth_differentiable_on (n - 1) Q (a - δ, a + δ)) as [Qn HQ].
      {
        unfold Q, Taylor_polynomial.
        apply nth_differentiable_on_sum; try lia.
        - apply differentiable_domain_open; lra.
        - intros k H6.
          apply nth_differentiable_on_mult_const_l. apply nth_differentiable_on_pow_shift. apply differentiable_domain_open; lra.
      }
      exists (fn - Qn)%function.
      apply nth_derivative_on_minus; auto.
      apply differentiable_domain_open; lra.
    + exists δ. split; auto. apply nth_derivative_on_imp_nth_differentiable_on with (fn := fun x => (n! / (n - (n-1))!) * (x - a)^(n - (n-1))).
      apply nth_derivative_imp_nth_derivative_on. apply differentiable_domain_open; lra.
      apply nth_derivative_pow_shift; lia.
    + intros k H6. rewrite nth_derive_at_minus; auto.
      2 : { apply nth_differentiable_at_le with (m := n); auto; lia. }
      2 : { 
        unfold Q, Taylor_polynomial.
        apply nth_differentiable_at_sum; try lia.
        intros k0 H7. apply nth_differentiable_at_mult_const_l. apply nth_differentiable_at_pow_shift; lia.
      }
      unfold Q. rewrite nth_derive_taylor_poly_eq; try lia. lra.
    + intros k H6. set (fn := fun x : R => 0). replace 0 with (fn a) by (auto). apply nth_derivative_at_imp_nth_derive_at.
      unfold fn. apply nth_derivative_at_pow_shift_zero; lia.
    + intros k H6. exists δ. split; auto. intros x H7 H8.
      assert (H9 : (S k <= n)%nat) by lia.
      pose proof (nth_derivative_pow_shift n (S k) a H9) as H10.
      apply nth_derivative_imp_nth_derive in H10.
      rewrite H10. assert (H11 : n! > 0) by apply INR_fact_lt_0.
      assert (H12 : (n - S k)! > 0) by apply INR_fact_lt_0.
      pose proof (Rdiv_pos_pos (n!) ((n - S k)!) H11 H12) as H13.
      assert (H14 : (n - S k) >= 0). { rewrite <- minus_INR; try lia. apply Rle_ge. apply pos_INR. }
      pose proof pow_nonzero (x - a) (n - S k) ltac:(lra) as H15. nra.
    + unfold C. apply limit_eq with (f1 := fun x => ((⟦ Der^(n - 1) ⟧ f) x - ⟦ Der^(n - 1) a ⟧ f) / (n! * (x - a))).
      {
        exists δ. split; try lra. intros x H6.
        replace ((⟦ Der^(n - 1) ⟧ (λ x0 : ℝ, (x0 - a) ^ n)) x) with ((⟦ Der^(n - 1) x ⟧ (λ x0 : ℝ, (x0 - a) ^ n))) by auto.
        replace ((⟦ Der^(n - 1) x ⟧ (λ x0 : ℝ, (x0 - a) ^ n))) with ((λ y, n! * (y - a)) x).
        2: {
          symmetry.
          apply (nth_derivative_at_imp_nth_derive_at (n - 1)%nat x (λ x0 : ℝ, (x0 - a) ^ n) ((λ y, n! * (x - a)))).
          eapply nth_derivative_at_ext_val.
          - apply nth_derivative_imp_at. apply nth_derivative_pow_shift; lia.
          - simpl. replace (n - (n - 1))%nat with 1%nat by lia. rewrite fact_1, pow_1, Rdiv_1_r. auto.
        }
        rewrite nth_derive_at_minus. do 2 f_equal. unfold Q. rewrite nth_derive_taylor_poly_const; auto.
        apply nth_differentiable_on_imp_nth_differentiable_at with (D := (a - δ, a + δ)); auto_interval.
        unfold Q, Taylor_polynomial. apply nth_differentiable_at_sum; try lia.
        intros k H7. apply nth_differentiable_at_mult_const_l. apply nth_differentiable_at_pow_shift; lia.
      }

      replace (λ x : ℝ, ((⟦ Der^(n - 1) ⟧ f) x - (⟦ Der^(n - 1) a ⟧ f)) / (n! * (x - a))) with (λ x : ℝ, (((⟦ Der^(n - 1) x ⟧ f) - (⟦ Der^(n - 1) a ⟧ f)) / (x - a)) * (1 / n!)).
      2 : {
        extensionality t. replace (((⟦ Der^(n - 1) ⟧ f) t)) with ((⟦ Der^(n - 1) t ⟧ f)) by auto.
        assert (t - a  = 0 \/ t - a <> 0) as [H16 | H16] by lra.
        - rewrite H16. rewrite Rmult_0_r, Rdiv_0_r. lra.
        - field. split; try lra. apply INR_fact_neq_0.
      }
      replace ((⟦ Der^n a ⟧ f) / n!) with ((⟦ Der^n a ⟧ f) * (1 / n!)) by lra.

      apply limit_mult_const_r.

  set (fn := λ x, ⟦ Der^(n - 1) x ⟧ f).
  set (fn' := (⟦ Der^n ⟧ f)).

  replace ((⟦ Der^n a ⟧ f)) with (fn' a) by auto.

  assert (H6 : ⟦ der a ⟧ fn = fn').
  {
    apply derive_at_spec.
    2 : { unfold fn, fn'. rewrite nth_derive_at_comm. rewrite <- nth_derive_at_succ. replace (S (n - 1)) with n by lia. reflexivity. }
    apply nth_differentiable_at_imp_differentiable_at_derive_pred; auto.
  }

  replace a with (0 + a) at 1 by lra.

  rewrite <- limit_shift with (a := 0)(c := a).
  replace (λ x : ℝ, (fn (x + a) - fn a) / (x + a - a)) with (λ x, ((fn (a + x) - fn a) / x)); auto.
  extensionality x. replace ((x + a) - a) with x by lra. rewrite Rplus_comm. reflexivity.
Qed.

Theorem theorem_20_2 : forall n a f, 
  (n > 0)%nat ->
  nth_differentiable_at n f a ->
  (forall k, (1 <= k < n)%nat -> ⟦ Der ^ k a ⟧ f = 0) -> 
  ⟦ Der ^ n a ⟧ f <> 0 -> 
  ( (Nat.Even n /\ ⟦ Der ^ n a ⟧ f > 0 -> local_minimum_point f ℝ a) /\ 
    (Nat.Even n /\ ⟦ Der ^ n a ⟧ f < 0 -> local_maximum_point f ℝ a) /\
    (Nat.Odd n -> ~ local_maximum_point f ℝ a /\ ~ local_minimum_point f ℝ a) ).
Proof.
  intros n a f H1 H2 H3 H4.

  assert (H5 : forall x, P(n, a, f) x = f a + (⟦ Der ^ n a ⟧ f) / n! * (x - a) ^ n).
  {
    intro x. unfold Taylor_polynomial.
    destruct (Nat.eq_dec n 1) as [H5 | H5].
    - subst n. rewrite sum_f_i_Sn_f; try lia.
      rewrite sum_f_0_0. simpl. lra.
    - replace n with (S (n - 1))%nat by lia.
      rewrite sum_f_i_Sn_f; try lia. rewrite sum_f_Si; try lia.
      rewrite sum_f_0; try lia.
      2 :
      {
        intros k H6. rewrite H3; try lia.
        unfold Rdiv. rewrite Rmult_0_l, Rmult_0_l. reflexivity.
      }
      replace (⟦ Der ^ 0 a ⟧ f / 0! * (x - a) ^ 0) with (f a); simpl; lra.
  }

  pose proof (theorem_20_1 n a f H1 H2) as H6.

  assert (H7 : ⟦ lim a ⟧ (fun x => (f x - f a) / (x - a)^n) = ⟦ Der ^ n a ⟧ f / n!).
  {
    apply limit_eq with (f1 := fun x => (f x - P(n, a, f) x) / (x - a)^n + (⟦ Der ^ n a ⟧ f / INR (fact n))).
    - exists 1. split; [lra|]. intros x H7.
      rewrite H5. field. split. apply pow_nonzero. solve_R. apply INR_fact_neq_0.
    - rewrite <- Rplus_0_l.
      replace ((⟦ Der^n a ⟧ f) / n!) with (0 + (⟦ Der^n a ⟧ f) / n!) by lra.
      apply limit_plus_const. apply H6.
  }

  set (C := ⟦ Der ^ n a ⟧ f / n!).

  assert (H8 : C <> 0).
  { unfold C. apply Rdiv_neq_0; try lra. apply INR_fact_neq_0. }

  assert (exists δ, δ > 0 /\ forall x, 0 < |x - a| < δ -> ((f x - f a) / (x - a) ^ n) * C > 0) as [δ1 [H9 H10]].
  {
    destruct (Rtotal_order C 0) as [H9 | [H9 | H9]]; try lra.
    - pose proof limit_neg_neighborhood _ _ _ H7 H9 as [δ [H10 H11]].
      exists δ. split; auto. intros x H12. specialize (H11 x H12).
      apply Rmult_neg_neg; auto.
    - pose proof limit_pos_neighborhood _ _ _ H7 H9 as [δ [H10 H11]].
      exists δ. split; auto. intros x H12. specialize (H11 x H12).
      apply Rmult_pos_pos; auto.
  }

  split; [| split].
  - intros [H11 H12]. 
    assert (H13 : C > 0). { unfold C. apply Rdiv_pos_pos; try lra. apply INR_fact_lt_0. }
    split; [ apply Full_intro | exists δ1; split; auto ].
    replace (ℝ ⋂ (a - δ1, a + δ1)) with ((a - δ1, a + δ1)).
    2 : { rewrite Intersection_comm, Intersection_Identity. auto. }
    split; [ solve_R | ].
    intros x H14. assert (x = a \/ x <> a) as [H15 | H15] by lra; subst; try lra.
    specialize (H10 x ltac:(solve_R)). 
    assert (H16 : (x - a) ^ n > 0) by (apply Rpow_even_gt_0; solve_R).
    pose proof (Rdiv_pos_pos_rev ((f x - f a)) ((x - a)^n) ltac:(nra)) H16. nra.
  - intros [H11 H12].
    assert (H13 : C < 0). { unfold C. apply Rdiv_neg_pos; try lra. apply INR_fact_lt_0. }
    split; [ apply Full_intro | exists δ1; split; auto ].
    replace (ℝ ⋂ (a - δ1, a + δ1)) with ((a - δ1, a + δ1)).
    2 : { rewrite Intersection_comm, Intersection_Identity. auto. }
    split; [ solve_R | ].
    intros x H14. assert (x = a \/ x <> a) as [H15 | H15] by lra; subst; try lra.
    specialize (H10 x ltac:(solve_R)). 
    assert (H16 : (x - a) ^ n > 0) by (apply Rpow_even_gt_0; solve_R).
    pose proof (Rdiv_neg_pos_rev ((f x - f a)) ((x - a)^n) ltac:(nra)) H16. nra.
  - intros H11.
    split; intros [H12 [δ2 [H13 [_ H14]]]]. 
    + rewrite Intersection_comm, Intersection_Identity in H14.
      set (δ := Rmin δ1 δ2).
      assert (C > 0 \/ C < 0) as [H15 | H15] by lra.
      * set (x := a + δ / 2).
        specialize (H10 x ltac:(unfold x, δ; solve_R)).
        assert (H16 : ( (x - a) ^ n) > 0). { apply Rpow_gt_0; unfold x, δ; solve_R. }
        pose proof (Rdiv_pos_pos_rev ((f x - f a)) ((x - a) ^ n) ltac:(nra)) H16 as H17.
        specialize (H14 x ltac:(unfold x, δ; solve_R)). lra.
      * set (x := a - δ / 2).
        specialize (H10 x ltac:(unfold x, δ; solve_R)).
        assert (H16 : ( (x - a) ^ n) < 0). { apply Rpow_odd_lt_0; unfold x, δ; solve_R. }
        pose proof (Rdiv_pos_neg_rev ((f x - f a)) ((x - a) ^ n) ltac:(nra)) H16 as H17.
        specialize (H14 x ltac:(unfold x, δ; solve_R)). lra.
    + rewrite Intersection_comm, Intersection_Identity in H14.
      set (δ := Rmin δ1 δ2).
      assert (C > 0 \/ C < 0) as [H15 | H15] by lra.
      * set (x := a - δ / 2).
        specialize (H10 x ltac:(unfold x, δ; solve_R)).
        assert (H16 : ( (x - a) ^ n) < 0). { apply Rpow_odd_lt_0; unfold x, δ; solve_R. }
        pose proof (Rdiv_pos_neg_rev' ((f x - f a)) ((x - a) ^ n) ltac:(nra)) H16 as H17.
        specialize (H14 x ltac:(unfold x, δ; solve_R)). lra.
      * set (x := a + δ / 2).
        specialize (H10 x ltac:(unfold x, δ; solve_R)).
        assert (H16 : ( (x - a) ^ n) > 0). { apply Rpow_gt_0; unfold x, δ; solve_R. }
        pose proof (Rdiv_neg_pos_rev ((f x - f a)) ((x - a) ^ n) ltac:(nra)) H16 as H17.
        specialize (H14 x ltac:(unfold x, δ; solve_R)). lra.
Qed.

Definition equal_up_to_order (n : nat) (f g : R -> R) (a : R) : Prop :=
  ⟦ lim a ⟧ (fun x => (f x - g x) / ((x - a) ^ n)) = 0.

Theorem theorem_20_3 : forall n a pl ql,
  let P := fun x => polynomial pl (x - a) in
  let Q := fun x => polynomial ql (x - a) in
  (length pl <= n + 1)%nat -> (length ql <= n + 1)%nat ->
  equal_up_to_order n P Q a ->
  P = Q.
Proof.
  intros n a pl ql P Q H1 H2 H3.
  generalize dependent ql.
  generalize dependent pl.
  induction n as [| k IH]. intros pl P H1 ql Q H2 H3.
  - destruct (poly_decompose pl) as [l1 [c1 [H4 H5]]].
    destruct (poly_decompose ql) as [l2 [c2 [H6 H7]]].
    assert (length l1 = 0%nat /\ length l2 = 0%nat) as [H8 H9] by lia.
    apply length_zero_iff_nil in H8, H9; subst. simpl in *.
    assert (H8 : c1 = c2).
    {
      unfold equal_up_to_order in H3.
      replace (fun x => (P x - Q x) / (x - a) ^ 0) with (fun x => P x - Q x) in H3 by (extensionality x; solve_R).
      assert (H8 : ⟦ lim a ⟧ (fun x => P x - Q x) = c1 - c2).
      {
        apply limit_eq' with (f1 := fun x => c1 - c2); [ | solve_lim ].
        intros x. unfold P, Q. rewrite H4, H6, poly_nil. lra.
      }
      apply limit_unique with (f := fun x => P x - Q x) (a := a) (L1 := c1 - c2) (L2 := 0) in H3; auto; lra.
    }
    extensionality x. unfold P, Q. rewrite H4, H6, poly_nil, Rmult_0_r, Rplus_0_l, Rplus_0_l. auto.
  - intros pl P H1 ql Q H2 H3.
    destruct (poly_decompose pl) as [l1 [c1 [H4 H5]]].
    destruct (poly_decompose ql) as [l2 [c2 [H6 H7]]].
    assert (H8 : c1 = c2).
    {
      unfold equal_up_to_order in H3.
      assert (H8 : ⟦ lim a ⟧ (fun x => P x - Q x) = 0).
      {
        apply limit_eq with (f1 := fun x => ((P x - Q x) / (x - a) ^ S k) * (x - a) ^ S k).
        - exists 1. split; [lra|]. intros x H8. field. apply pow_nonzero. solve_R.
        - replace 0 with (0 * ((a - a) ^ S k)) by lra. apply limit_mult; solve_lim.
      }
      assert (H9 : ⟦ lim a ⟧ (fun x => P x - Q x) = c1 - c2).
      {
        apply limit_eq' with (f1 := fun x => (x - a) * polynomial l1 (x - a) + c1 - ((x - a) * polynomial l2 (x - a) + c2)).
        - intros x. unfold P, Q. rewrite H4, H6. reflexivity.
        - replace (c1 - c2) with (0 + (c1 - c2)) by lra.
          replace (fun x => (x - a) * polynomial l1 (x - a) + c1 - ((x - a) * polynomial l2 (x - a) + c2))
          with (fun x => (x - a) * (polynomial l1 (x - a) - polynomial l2 (x - a)) + (c1 - c2)) by (extensionality x; lra).
          apply limit_plus; [ | solve_lim ].
          replace 0 with ((a - a) * (polynomial l1 (a - a) - polynomial l2 (a - a))) by lra.
          apply limit_mult; [ solve_lim | ].
          apply limit_minus; (apply limit_continuous_comp; [ solve_lim | apply continuous_at_polynomial ]).
      }
      apply limit_unique with (f := fun x => P x - Q x) (a := a) (L1 := c1 - c2) (L2 := 0) in H8; auto. lra.
    }
    subst c2.
    assert (H11 : (fun x => polynomial l1 (x - a)) = (fun x => polynomial l2 (x - a))).
    {
      apply IH; try lia.
      unfold equal_up_to_order in *.
      apply limit_eq with (f1 := fun x => (P x - Q x) / (x - a) ^ S k); auto.
      exists 1. split; [lra|]. intros x H8. unfold P, Q. rewrite H4, H6. simpl. field; split; [apply pow_nonzero|]; solve_R.
    }
    extensionality x. unfold P, Q. rewrite H4, H6. rewrite <- (equal_f H11 x). reflexivity.
Qed.

Lemma Taylor_is_polynomial : forall n a f, 
  exists l, length l = S n /\ (forall x, polynomial l (x - a) = P(n, a, f) x).
Proof.
  intros n a f.
  induction n as [| k IH].
  - exists [f a]. split; simpl; try lia.
    intro x. unfold Taylor_polynomial. rewrite sum_f_0_0.
    rewrite fact_0, Rdiv_1_r, pow_O, Rmult_1_r. simpl. rewrite poly_cons, poly_nil; solve_R.
  - destruct IH as [l [H1 H2]].
    exists ((⟦ Der ^ (S k) a ⟧ f / (S k)!) :: l). split.
    + simpl. lia.
    + intro x. rewrite poly_cons. rewrite H1. rewrite H2.
      unfold Taylor_polynomial. rewrite sum_f_i_Sn_f; try lia.
      rewrite Rplus_comm. reflexivity. 
Qed.

Corollary corollary_20_1 : forall n a f l,
  let P := fun x => polynomial l (x - a) in
  (n > 0)%nat ->
  nth_differentiable_at n f a ->
  (length l <= n + 1)%nat ->
  equal_up_to_order n f P a ->
  P = P(n, a, f).
Proof.
  intros n a f l P H1 H2 H3 H4.
  destruct (Taylor_is_polynomial n a f) as [ql [H5 H6]].
  set (Q := fun x => polynomial ql (x - a)).
  assert (H7 : P(n, a, f) = Q).
  { extensionality x. symmetry. apply H6. }
  assert (H8 : equal_up_to_order n f Q a).
  {
    unfold equal_up_to_order.
    rewrite <- H7.
    apply theorem_20_1; auto.
  }
  assert (H9 : equal_up_to_order n P Q a).
  {
    unfold equal_up_to_order in *.
    apply limit_eq with (f1 := fun x => ((P x - f x) / (x - a) ^ n) + ((f x - Q x) / (x - a) ^ n)).
    - exists 1. split; [lra|]. intros x H9. field. apply pow_nonzero. solve_R.
    - replace 0 with (0 + 0) by lra. apply limit_plus; auto.
      apply limit_eq' with (f1 := fun x => -1 * ((f x - P x) / (x - a)^n)); solve_R.
      replace 0 with (-1 * 0) by lra. apply limit_mult_const_l; auto.
  }
  rewrite H7. apply theorem_20_3 with (n := n) (a := a) (pl := l) (ql := ql); solve_R.
Qed.

Lemma lemma_20_1 : forall n a b g,
  a < b ->
  nth_differentiable_on (S n) g [a, b] ->
  (forall k, (k <= n)%nat -> ⟦ Der ^ k ⟧ g [a, b] a = 0) ->
  forall x, x ∈ (a, b] ->
  exists t, t ∈ (a, x) /\
    g x / (x - a) ^ (S n) = (⟦ Der ^ (S n) t ⟧ g) / (S n)!.
Proof.
  induction n as [| k IH].
  - intros a b g H1 H2 H3 x H4.
    assert (H5 : g a = 0).
    { specialize (H3 0%nat ltac:(lia)). simpl in H3. auto. }
    assert (H6 : continuous_on g [a, x]).
    {
      apply differentiable_on_imp_continuous_on_subset with (D1 := [a, b]).
      - apply nth_differentiable_on_imp_differentiable_on with (n := 1%nat); auto.
      - apply differentiable_domain_closed; solve_R.
      - intros y Hy. solve_R.
    }
    assert (H7 : differentiable_on g (a, x)).
    {
      apply differentiable_on_subset_open with (a := a) (b := b); try solve_R.
      apply nth_differentiable_on_imp_differentiable_on with (n := 1%nat); auto.
      apply nth_differentiable_on_subset with (D1 := [a, b]); auto.
      - apply differentiable_domain_open; lra.
      - intros y H7. solve_R.
    }
    pose proof (mean_value_theorem g a x (ltac:(solve_R)) H6 H7) as [t [H8 H9]].
    exists t. split; auto.
    rewrite H5, Rminus_0_r in H9.
    rewrite fact_1, pow_1, Rdiv_1_r, nth_derive_1.
    replace ((⟦ Der ⟧ g) t) with (⟦ Der t ⟧ g) by auto.
    symmetry. apply derive_at_spec in H9; auto.
    apply differentiable_on_imp_differentiable_at with (D := (a, x)); auto_interval.
  - intros a b g H1 H2 H3 x H4.
    set (n := S k).
    set (h := fun y => (y - a) ^ (S n)).
    assert (H5 : continuous_on g [a, x]).
    {
      apply differentiable_on_imp_continuous_on_subset with (D1 := [a, b]).
      - apply nth_differentiable_on_imp_differentiable_on with (n := S n); auto; lia.
      - apply differentiable_domain_closed; solve_R.
      - intros y Hy. solve_R.
    }
    assert (H6 : continuous_on h [a, x]).
    { unfold h. apply continuous_on_pow_shift. }
    assert (H7 : differentiable_on g (a, x)).
    {
      apply differentiable_on_subset_open with (a := a) (b := b); try solve_R.
      apply nth_differentiable_on_imp_differentiable_on with (n := S n); auto; try solve_R.
      apply nth_differentiable_on_subset with (D1 := [a, b]); auto.
      - apply differentiable_domain_open; lra.
      - intros y H7. solve_R.
    }
    assert (H8 : differentiable_on h (a, x)).
    { unfold h. apply differentiable_on_pow_shift. apply differentiable_domain_open; solve_R. }
    assert (H9 : ∀ x0 : ℝ, x0 ∈ (a, x) → (⟦ Der ⟧ h (a, x)) x0 ≠ 0).
    {
      intros y H9. unfold h. pose proof (derive_at_pow_shift (S n) a y) as H10.
      rewrite derive_on_eq_derive_at_interior; [ | auto_interval ].
      replace ((⟦ Der ⟧ (λ x : ℝ, (x - a) ^ S n)) y) with (⟦ Der y ⟧ (λ x : ℝ, (x - a) ^ S n)) by auto.
      rewrite H10. replace (S n - 1)%nat with n by lia. pose proof pow_nonzero (y - a) n ltac:(solve_R) as H11.
      pose proof not_0_INR (S n) ltac:(lia) as H12. nra.
    }
    assert (H10 : h x <> h a).
    {
      unfold h. replace (a - a) with 0 by lra.
      rewrite pow_i; try (unfold n; lia).
      apply pow_nonzero; solve_R.
    }
    
    pose proof (cauchy_mvt g (⟦ Der ⟧ g (a, x)) h (⟦ Der ⟧ h (a, x)) a x (ltac:(solve_R)) H5 H6) as H11.
    assert (H12 : ⟦ der ⟧ g (a, x) = ⟦ Der ⟧ g (a, x)).
    { apply derive_on_spec; auto. }
    assert (H13 : ⟦ der ⟧ h (a, x) = ⟦ Der ⟧ h (a, x)).
    { apply derive_on_spec; auto. }
    specialize (H11 H12 H13 H9 H10) as [z [H14 H15]].
    
    set (g' := ⟦ Der ⟧ g [a, b]).

    specialize (IH a z g' ltac:(solve_R)).

    assert (H16 : nth_differentiable_on (S k) g' [a, z]).
    {
        unfold g'.
        apply nth_differentiable_on_subset with (D1 := [a, b]).
        - apply nth_differentiable_on_derive; auto.
          apply differentiable_domain_closed; solve_R.
        - apply differentiable_domain_closed; solve_R.
        - intros y H16. solve_R.
    }
    assert (H17 : forall j, (j <= k)%nat -> ⟦ Der ^ j ⟧ g' [a, z] a = 0).
    {
      intros j H18. unfold g' in *.

      rewrite nth_derive_on_subset with (D1 := [a, b]).
      - rewrite <- nth_derive_on_succ. apply H3. lia.
      - apply differentiable_domain_closed; solve_R.
      - intros y H19. solve_R.
      - solve_R.
      - apply nth_differentiable_on_le with (m := S k); try lia.
        apply nth_differentiable_on_derive; auto.
        apply differentiable_domain_closed; solve_R.
    }
    assert (H18 : z ∈ (a, z]). { split; solve_R. }
    
    specialize (IH H16 H17 z H18) as [t [H19 H20]].

    exists t. split; [solve_R | ].
    
    rewrite derive_on_open_eq_derive with (D := (a, x)) (x := z) in H15; try solve [auto_interval].
    rewrite derive_on_open_eq_derive with (D := (a, x)) (x := z) in H15; try solve [auto_interval].
    
    unfold h in H15. rewrite derive_at_pow_shift in H15.
    unfold n in H15. replace (S (S k) - 1)%nat with (S k) in H15 by lia.
    
    assert (H21 : g' z = ⟦ Der z ⟧ g).
    { unfold g'. apply derive_on_eq_derive_at_interior with (D := [a, b]); auto_interval. }
    replace ((⟦ Der ⟧ g) z) with (⟦ Der z ⟧ g) in H15 by auto.
    rewrite <- H21, Rminus_diag, pow_i, Rminus_0_r in H15; try lia.
    replace (g' z / (S (S k) * (z - a) ^ S k)) with ((g' z / (z - a) ^ S k) / S (S k)) in H15.
    2 : { field. split. apply pow_nonzero; solve_R. apply not_0_INR; lia. }
    
    rewrite H20 in H15.
    
    assert (H22 : ⟦ Der ^ (S k) t ⟧ g' = ⟦ Der ^ (S n) t ⟧ g).
    {
      unfold g', n. repeat rewrite nth_derive_at_succ.
      apply nth_derive_at_eq with (δ := Rmin (t - a) (b - t)); [ solve_R | ].
      intros y H22. apply derive_at_eq. exists (Rmin (y - a) (b - y)).
      split; [ solve_R | ].
      intros w H23.
      apply derive_on_eq_derive_at_interior. auto_interval.
    }
    rewrite H22 in H15. replace (g a) with 0 in H15 by (specialize (H3 0%nat ltac:(lia)); auto).
    rewrite Rminus_0_r in H15. unfold n in *. rewrite H15.
    repeat rewrite fact_simpl.
    assert (H23 : INR (k!) <> 0). { apply not_0_INR. apply fact_neq_0. }
    pose proof (pos_INR k) as H24. solve_R.
Qed.

Theorem Taylors_Theorem : forall n a x f,
  a < x ->
  (exists δ, δ > 0 /\ nth_differentiable_on (S n) f (a - δ, x + δ)) ->
  exists t, t ∈ (a, x) /\ R(n, a, f) x = (⟦ Der ^ (n + 1) t ⟧ f) / ((n + 1)!) * (x - a) ^ (n + 1).
Proof.
  intros n a x f H1 [δ [H0 H2']].
  assert (H2 : nth_differentiable_on (S n) f [a, x]).
  {
    apply nth_differentiable_on_subset with (D1 := (a - δ, x + δ)); auto.
    - apply differentiable_domain_closed; lra.
    - intros y H3. solve_R.
  }
  replace (n + 1)%nat with (S n) by lia.
  
  set (g := R(n, a, f)).

  assert (H3 : nth_differentiable_on (S n) g [a, x]).
  {
    unfold g, Taylor_remainder.
    apply nth_differentiable_on_minus; auto; try lia.
    unfold Taylor_polynomial.
    apply nth_differentiable_on_sum; try lia.
    - apply differentiable_domain_closed; lra.
    - intros k H3.
      apply nth_differentiable_on_mult_const_l.
      apply nth_differentiable_on_pow_shift.
      apply differentiable_domain_closed; lra.
  }

  assert (H4 : forall k, (k <= n)%nat -> ⟦ Der ^ k ⟧ g [a, x] a = 0).
  {
    intros k H4.
    unfold g, Taylor_remainder.
    
    rewrite nth_derive_on_minus.
    2 : { apply differentiable_domain_closed; lra. }
    2 : { solve_R. }
    2: { apply nth_differentiable_on_le with (m := S n); try lia; auto. }
    2: {
        apply nth_differentiable_on_le with (m := S n) (f := P(n, a, f)); try lia; auto. unfold Taylor_polynomial.
        apply nth_differentiable_on_sum; try lia.
         - apply differentiable_domain_closed; lra.
         - intros j H5.
           apply nth_differentiable_on_mult_const_l.
           apply nth_differentiable_on_pow_shift.
           apply differentiable_domain_closed; lra.
    }

    assert (H5 : ⟦ Der ^ k ⟧ (P(n, a, f)) [a, x] a = ⟦ Der ^ k a ⟧ f).
    {
      unfold Taylor_polynomial.
      rewrite nth_derive_on_sum; try (apply differentiable_domain_closed; lra); try lia; try solve [solve_R].
      2: { intros j H5. apply nth_differentiable_on_mult_const_l. apply nth_differentiable_on_pow_shift. apply differentiable_domain_closed; lra. }
      
      rewrite sum_single_index with (k := k); try lia.
      - rewrite nth_derive_on_mult_const_l; try (apply differentiable_domain_closed; lra); try (split; lra).
        2: { apply nth_differentiable_on_pow_shift. apply differentiable_domain_closed; lra. }
        assert (H5 : ⟦ Der ^ k ⟧ (λ x0 : ℝ, (x0 - a) ^ k) [a, x] a = k!).
        {
          assert (H5 : differentiable_domain [a, x]) by (apply differentiable_domain_closed; lra).
          assert (H6 : ⟦ der^k ⟧ (λ x0 : ℝ, (x0 - a) ^ k) [a, x] = (λ _ : ℝ, k!)).
          {
            pose proof nth_derivative_on_pow_shift k k a [a, x] H5 ltac:(lia) as H6.
            replace (λ x : ℝ, INR (k!) / INR ((k - k)!) * (x - a) ^ (k - k)) with (λ _ : ℝ, INR (k!)) in H6.
            2: { extensionality y. rewrite Nat.sub_diag, pow_O, Rdiv_1_r. lra. }
            apply H6.
          }

          pose proof (nth_derivative_on_imp_nth_derive_on k (λ x0 : ℝ, (x0 - a) ^ k) (fun _ => k!) [a, x] H5 H6) as H7.
          specialize (H7 a ltac:(solve_R)). apply H7.
        }
        rewrite H5.
        field. apply INR_fact_neq_0.
      - intros j H6 H7. rewrite nth_derive_on_mult_const_l.
        2: { apply differentiable_domain_closed; lra. }
        2: { split; lra. }
        2: { apply nth_differentiable_on_pow_shift. apply differentiable_domain_closed; lra. }

        apply Rmult_eq_0_compat_l.
        assert (j < k \/ j > k)%nat as [H8 | H8] by lia.
        + rewrite nth_derivative_on_imp_nth_derive_on with (f' := fun _ => 0); try solve [solve_R].
          * apply differentiable_domain_closed; lra.
          * apply nth_derivative_imp_nth_derivative_on; try (apply differentiable_domain_closed; lra).
            apply nth_derivative_pow_shift_gt; auto.
        + rewrite nth_derivative_on_imp_nth_derive_on with (f' := fun x => (INR (fact j) / INR (fact (j - k))) * (x - a) ^ (j - k)); try solve [solve_R].
          * rewrite Rminus_diag. rewrite pow_i; try lia; lra.
          * apply differentiable_domain_closed; lra.
          * apply nth_derivative_imp_nth_derivative_on; try (apply differentiable_domain_closed; lra).
            apply nth_derivative_pow_shift; lia.
    }

    rewrite H5, nth_derive_on_subset with (D1 := (a - δ, x + δ)); try solve [solve_R].
    - rewrite nth_derive_on_eq_nth_derive_at_interior; try solve [auto_interval].
      apply nth_differentiable_on_le with (m := S n); auto.
    - apply differentiable_domain_closed; lra.
    - intros y H6. solve_R.
    - apply nth_differentiable_on_le with (m := S n); auto.
  }

  pose proof (lemma_20_1 n a x g H1 H3 H4 x ltac:(split; lra)) as [t [H5 H6]].
  exists t. split; auto.

  assert (H7 : ⟦ Der ^ (S n) t ⟧ g = ⟦ Der ^ (S n) t ⟧ f).
  {
    unfold g, Taylor_remainder.
    rewrite nth_derive_at_minus.
    2: { apply nth_differentiable_on_imp_nth_differentiable_at with (D := [a, x]); auto_interval. }
    2: {
      unfold Taylor_polynomial.
      apply nth_differentiable_at_sum; try lia.
      intros i Hi. apply nth_differentiable_at_mult_const_l.
      apply nth_differentiable_at_pow_shift.
    }
    
    replace (⟦ Der ^ (S n) t ⟧ (P(n, a, f))) with 0; try lra.
    unfold Taylor_polynomial.
    rewrite nth_derive_at_sum; try lia.
    2: { intros k. apply nth_differentiable_mult_const_l. apply nth_differentiable_pow_shift. }
    rewrite sum_f_0; try solve [solve_R].
    intros k H7.
    rewrite nth_derive_mult_const_l.
    rewrite nth_derive_pow_shift_gt; try lia. lra.
    apply nth_differentiable_pow_shift.
  }

  rewrite H7 in H6. apply Rmult_eq_compat_r with (r := (x - a) ^ S n) in H6.
  field_simplify in H6. 2 : { apply INR_fact_neq_0. } 2 : { apply pow_nonzero. lra. }
  rewrite H6.
  field. apply INR_fact_neq_0.
Qed.

Lemma cos_1_bounds : 0.540 < cos 1 < 0.541.
Proof.
  assert (H1 : exists δ, δ > 0 /\ nth_differentiable_on (S 6) cos (0 - δ, 1 + δ)).
  {
    exists 1. split; [lra |].
    apply nth_differentiable_imp_nth_differentiable_on.
    - apply differentiable_domain_open; lra.
    - apply inf_differentiable_imp_nth_differentiable. apply inf_differentiable_cos.
  }
  pose proof (Taylors_Theorem 6 0 1 cos ltac:(lra) H1) as [t [H2 H3]].
  assert (H4 : P(6, 0, cos) 1 = 389/720).
  {
     unfold Taylor_polynomial.
     repeat rewrite sum_f_i_Sn_f; try lia.
     rewrite sum_f_0_0; try lia.
     simplify_factorials.
     simplify_nth_derive_trig. repeat rewrite sin_0, cos_0.
     simpl; lra.
  }
  unfold Taylor_remainder in H3.
  rewrite H4 in H3.
  assert (H5 : ⟦ Der ^ (S 6) t ⟧ cos = sin t).
  {
    replace (⟦ Der ^ 7 t ⟧ cos) with ((⟦ Der ^ 7 ⟧ cos) t) by reflexivity.
    simplify_nth_derive_trig; auto.
  }
  replace (6 + 1)%nat with 7%nat in H3 by lia.
  rewrite H5 in H3.
  replace (INR ((S 6)!)) with 5040 in H3 by (simplify_factorials; auto). 
  rewrite Rminus_0_r in H3.
  rewrite pow1 in H3.
  rewrite Rmult_1_r in H3.
  assert (H6 : -1 <= sin t <= 1) by (apply sin_bounds; solve_R).
  replace (cos 1) with (389 / 720 + sin t / 5040) by lra.
  split.
  - apply Rplus_lt_reg_r with (r := -389/720); apply Rmult_lt_reg_r with (r := 5040); [ lra |].
    field_simplify. rewrite Rmult_div_r; auto. replace ((3628800 * 0.540 - 1960560) / 720) with (-1.4) by lra. lra.
  - apply Rplus_lt_reg_r with (r := -389/720); apply Rmult_lt_reg_r with (r := 5040); [ lra |].
    field_simplify. rewrite Rmult_div_r; auto. replace ((3628800 * 0.541 - 1960560) / 720) with 3.64 by lra. lra.
Qed.

Lemma cos_2_bounds : -0.417 < cos 2 < -0.416.
Proof.
  assert (H1 : exists δ, δ > 0 /\ nth_differentiable_on (S 10) cos (0 - δ, 2 + δ)).
  {
    exists 1. split; [lra |].
    apply nth_differentiable_imp_nth_differentiable_on.
    - apply differentiable_domain_open; lra.
    - apply inf_differentiable_imp_nth_differentiable. apply inf_differentiable_cos.
  }
  pose proof (Taylors_Theorem 10 0 2 cos ltac:(lra) H1) as [t [H2 H3]].
  assert (H4 : P(10, 0, cos) 2 = -1510144 / 3628800).
  {
     unfold Taylor_polynomial.
     repeat rewrite sum_f_i_Sn_f; try lia.
     rewrite sum_f_0_0; try lia.
     simplify_factorials.
     simplify_nth_derive_trig.
     repeat rewrite sin_0, cos_0.
     simpl; lra.
  }
  unfold Taylor_remainder in H3.
  rewrite H4 in H3.
  assert (H5 : ⟦ Der ^ (S 10) t ⟧ cos = sin t).
  {
    replace (⟦ Der ^ 11 t ⟧ cos) with ((⟦ Der ^ 11 ⟧ cos) t) by reflexivity.
    simplify_nth_derive_trig; auto.
  }
  replace (10 + 1)%nat with 11%nat in H3 by lia.
  rewrite H5 in H3.
  replace (INR ((S 10)!)) with 39916800 in H3 by (simplify_factorials; auto).
  rewrite Rminus_0_r in H3.
  assert (H6 : -1 <= sin t <= 1) by (apply sin_bounds; solve_R). lra.
Qed.

Lemma e_bound_1_3 : 1 < exp 1 < 3.
Proof.
  split.
  - rewrite <- exp_0 at 1. apply exp_increasing; solve_R; apply Full_intro.
  - assert (H1 : exists δ, δ > 0 /\ nth_differentiable_on 3 exp (0 - δ, 1 + δ)).
    {
      exists 1. split; [lra |].
      apply nth_differentiable_imp_nth_differentiable_on.
      - apply differentiable_domain_open; lra.
      - apply inf_differentiable_imp_nth_differentiable; apply inf_differentiable_exp.
    }
    destruct H1 as [δ [H2 H3]].
    pose proof (Taylors_Theorem 2 0 1 exp ltac:(lra) (ex_intro _ δ (conj H2 H3))) as [t [H4 H5]].
    assert (H6 : P(2, 0, exp) 1 = 5/2).
    {
      unfold Taylor_polynomial.
      repeat rewrite sum_f_i_Sn_f; try lia.
      rewrite sum_f_0_0; try lia.
      repeat rewrite nth_derive_exp_n_0.
      simplify_factorials.
      field.
    }
    unfold Taylor_remainder in H5.
    rewrite H6 in H5.
    replace (2 + 1)%nat with 3%nat in H5 by lia.
    rewrite Rminus_0_r, pow1, Rmult_1_r in H5.
    replace (⟦ Der ^ 3 t ⟧ exp) with (exp t) in H5 by (rewrite nth_derive_exp; auto).
    replace (INR (3!)) with 6 in H5 by (simplify_factorials; lra).
    assert (H7 : exp t < exp 1).
    { apply exp_increasing; solve_R; apply Full_intro. }
    lra.
Qed.

Lemma e_bounds : 2.7182 < e < 2.7183.
Proof.
  assert (H1 : exists δ, δ > 0 /\ nth_differentiable_on (S 8) exp (0 - δ, 1 + δ)).
  {
    exists 1. split; [lra |].
    apply nth_differentiable_imp_nth_differentiable_on.
    - apply differentiable_domain_open; lra.
    - apply inf_differentiable_imp_nth_differentiable; apply inf_differentiable_exp.
  }
  pose proof (Taylors_Theorem 8 0 1 exp ltac:(lra) H1) as [t [H2 H3]].
  assert (H4 : P(8, 0, exp) 1 = 109601/40320).
  {
     unfold Taylor_polynomial.
     repeat rewrite sum_f_i_Sn_f; try lia.
     rewrite sum_f_0_0; try lia.
     repeat rewrite nth_derive_exp_n_0.
     simplify_factorials.
     field.
  }
  unfold Taylor_remainder in H3.
  rewrite H4 in H3.
  assert (H5 : ⟦ Der ^ (S 8) t ⟧ exp = exp t).
  {
    replace (⟦ Der ^ 9 t ⟧ exp) with ((⟦ Der ^ 9 ⟧ exp) t) by reflexivity.
    rewrite nth_derive_exp; auto.
  }
  replace (8 + 1)%nat with 9%nat in H3 by lia.
  rewrite H5 in H3.
  replace (INR ((S 8)!)) with 362880 in H3 by (simplify_factorials; lra).
  rewrite Rminus_0_r, pow1, Rmult_1_r in H3.
  assert (H6 : 1 < exp t < 3).
  {
    pose proof e_bound_1_3 as [H6 H7]. split.
    - rewrite <- exp_0. apply exp_increasing; solve_R; apply Full_intro.
    - pose proof exp_increasing t 1 ltac:(apply Full_intro) ltac:(apply Full_intro) ltac:(solve_R) as H8.
      lra.
  }
  unfold e. lra.
Qed.

Lemma e_bounds_crazy : 2.7182818284590452353602874713526624977572470936999595749669676277240766303535475945713821785251664274274663919320030599218174135966290435729003342952605956307381 < e < 2.7182818284590452353602874713526624977572470936999595749669676277240766303535475945713821785251664274274663919320030599218174135966290435729003342952605956307384.
Proof.
  assert (H1 : exists δ, δ > 0 /\ nth_differentiable_on (S 100) exp (0 - δ, 1 + δ)).
  {
    exists 1. split; [lra |].
    apply nth_differentiable_imp_nth_differentiable_on.
    - apply differentiable_domain_open; lra.
    - apply inf_differentiable_imp_nth_differentiable; apply inf_differentiable_exp.
  }
  pose proof (Taylors_Theorem 100 0 1 exp ltac:(lra) H1) as [t [H2 H3]].
  assert (H4 : P(100, 0, exp) 1 = 4299778907798767752801199122242037634663518280784714275131782813346597523870956720660008227544949996496057758175050906671347686438130409774741771022426508339/1581800261761765299689817607733333906622304546853925787603270574495213559207286705236295999595873191292435557980122436580528562896896000000000000000000000000).
  {
     unfold Taylor_polynomial.
     repeat rewrite sum_f_i_Sn_f; try lia.
     rewrite sum_f_0_0; try lia.
     repeat rewrite nth_derive_exp_n_0.
     simplify_factorials.
     field.
  }
  unfold Taylor_remainder in H3.
  rewrite H4 in H3.
  assert (H5 : ⟦ Der ^ (S 100) t ⟧ exp = exp t).
  {
    replace (⟦ Der ^ 101 t ⟧ exp) with ((⟦ Der ^ 101 ⟧ exp) t) by reflexivity.
    rewrite nth_derive_exp; auto.
  }
  replace (100 + 1)%nat with 101%nat in H3 by lia.
  rewrite H5 in H3.
  replace (INR ((S 100)!)) with 9425947759838359420851623124482936749562312794702543768327889353416977599316221476503087861591808346911623490003549599583369706302603264000000000000000000000000 in H3 by (simplify_factorials; lra).
  rewrite Rminus_0_r, pow1, Rmult_1_r in H3.
  assert (H6 : 1 < exp t < 3).
  {
    pose proof e_bound_1_3 as [H6 H7]. split.
    - rewrite <- exp_0. apply exp_increasing; solve_R; apply Full_intro.
    - pose proof exp_increasing t 1 ltac:(apply Full_intro) ltac:(apply Full_intro) ltac:(solve_R) as H8.
      lra.
  }
  unfold e. lra.
Qed.