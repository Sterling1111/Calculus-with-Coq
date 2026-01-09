From Lib Require Import Imports Notations Reals_util Functions Sums Sets Limit Continuity Derivative Trigonometry Interval Binomial.
Import Function_Notations LimitNotations DerivativeNotations SetNotations IntervalNotations.

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
      exists (fn - Qn)%f.
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

  induction n as [| k IH].
  - intros pl P H1 ql Q H2 H3. unfold equal_up_to_order in H3.
    replace (λ x : ℝ, (P x - Q x) / (x - a) ^ 0) with (λ x : ℝ, P x - Q x) in H3.
    2 : { extensionality x. rewrite pow_O. lra. }
    simpl in H1, H2.j
    simpl. lra. 
Admitted.

Corollary corollary_20_1 : forall n a f l,
  let P := fun x => polynomial l (x - a) in
  nth_differentiable n f ->
  (length l <= n + 1)%nat ->
  equal_up_to_order n f P a ->
  P = P(n, a, f).
Proof.
  intros n a f l P H1 H2 H3. admit.
Admitted.

Lemma lemma_20_1 : forall n a b f,
  a < b ->
  nth_differentiable_on (S n) (R(n, a, f)) [a, b] ->
  (forall k, (k <= n)%nat -> ⟦ Der ^ k a ⟧ (R(n, a, f)) = 0) ->
  forall x, x ∈ (a, b] ->
  exists t, t ∈ (a, x) /\
    (R(n, a, f) x) / (x - a) ^ (S n) = (⟦ Der ^ (S n) t ⟧ (R(n, a, f))) / (S n)!.
Proof.
  intros n a b f H1 H2 H3 x H4. admit.
Admitted.

Theorem Taylors_Theorem : forall n a x f,
  a < x ->
  nth_differentiable_on (n + 1) f [a, x] ->
  exists t, t ∈ (a, x) /\ R(n, a, f) x = (⟦ Der ^ (n + 1) t ⟧ f) / ((n + 1)!) * (x - a) ^ (n + 1).
Proof.
  intros n a x f H1 H2.
  admit.
Admitted.

Lemma cos_1_bounds : 0.5 < cos 1 < 0.542.
Proof.
  pose proof (Taylors_Theorem 3 0 1 cos) as H_thm.
  
  assert (H_lt : 0 < 1) by lra.
  assert (H_diff : nth_differentiable_on (3 + 1) cos [0, 1]).
  {
    admit. 
  }
  
  specialize (H_thm H_lt H_diff).
  destruct H_thm as [t [H_t_range H_eq]].
  assert (H_poly : P(3, 0, cos) 1 = 1/2).
  {
     unfold Taylor_polynomial.
     admit.
  }

  unfold Taylor_remainder in H_eq.
  rewrite H_poly in H_eq.
  
  assert (H_deriv_4 : ⟦ Der ^ (3 + 1) t ⟧ cos = cos t).
  { 
    replace (3 + 1)%nat with 4%nat by lia.
    admit. 
  }
  
  rewrite H_deriv_4 in H_eq.
  replace ((3 + 1)!) with (24%nat) in H_eq by reflexivity.
  Set Printing Coercions.
  replace (INR 24%nat) with 24 in H_eq by (simpl; lra).
  
  replace (1 - 0) with 1 in H_eq by lra.
  rewrite pow1 in H_eq.
  rewrite Rmult_1_r in H_eq.
  
  assert (H_bound : 0 < cos t < 1).
  {
    split; admit.
  }
  lra.
Admitted.