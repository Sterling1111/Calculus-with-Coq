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
  intros n a f.
  extensionality x.
  unfold Taylor_polynomial.
  
  rewrite nth_derive_sum; try lia.
  2: { 
    intros k. assert ((k < n)%nat \/ (k >= n)%nat) as [H1 | H1] by lia.
    - apply nth_derivative_imp_nth_differentiable with (fn := λ _, ((⟦ Der^k a ⟧ f) / k!) * 0).
      apply nth_derivative_mult_const_l. apply nth_derivative_pow_shift_gt; lia.
    - apply nth_derivative_imp_nth_differentiable with (fn := λ x, ((⟦ Der^k a ⟧ f) / k!) * ((INR (fact k) / INR (fact (k - n))) * (x - a) ^ (k - n))).
      apply nth_derivative_mult_const_l. apply nth_derivative_pow_shift; lia.
  }

  destruct n.
  - simpl. rewrite sum_f_n_n. simpl. lra.
  - rewrite sum_f_i_Sn_f; try lia.
    rewrite Rplus_comm.
    replace (∑ 0 n (λ k : ℕ, (⟦ Der ^ (S n) ⟧ (λ x0 : ℝ, ⟦ Der ^ k a ⟧ f / k! * (x0 - a) ^ k)) x)) with 0.
    2: {
      rewrite sum_f_0; try lia; try lra. intros k H1.
      (* 1. Define the constant C to simplify the expression *)
set (C := (⟦ Der^k a ⟧ f) / k!).

rewrite (nth_derivative_imp_nth_derive (S n) _ (λ _, 0)); auto.
replace ( λ _ : ℝ, 0) with  (λ _ : ℝ, C * 0) by (extensionality t; lra).
apply nth_derivative_mult_const_l.
  apply nth_derivative_pow_shift_gt; lia.
    }
    set (C := (⟦ Der^(S n) a ⟧ f) / (S n)!).

replace (⟦ Der^(S n) a ⟧ f) with (C * (S n)!).
2: {
  unfold C, Rdiv.
  rewrite Rmult_assoc.
  rewrite Rinv_l; [| apply INR_fact_neq_0].
  rewrite Rmult_1_r. reflexivity.
}

replace (λ x0, C * (x0 - a) ^ S n) with (fun x0 => C * (x0 - a) ^ S n).
2: { extensionality t. reflexivity. }

(* 3. Compute the derivative using the link to 'der' lemmas *)
rewrite (nth_derivative_imp_nth_derive (S n) _ (λ _, C * (S n)!)); try lra.
  apply nth_derivative_mult_const_l.
  replace (λ _ : ℝ, INR (fact (S n)))
   with (λ x : ℝ, INR (fact (S n)) / INR (fact (S n - S n)) * (x - a) ^ (S n - S n)).
2: {
  extensionality t.
  (* Simplify the algebra: S n - S n = 0 *)
  rewrite Nat.sub_diag.
  (* 0! = 1, (x-a)^0 = 1 *)
  rewrite fact_0, pow_O, Rdiv_1_r. lra.
}

(* 2. Now the goal matches the lemma exactly *)
apply nth_derivative_pow_shift.
lia. (* Prove S n <= S n *)
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
    + exists δ. split; auto. admit.
    + exists δ. split; auto. apply nth_derivative_on_imp_nth_differentiable_on with (fn := fun x => (n! / (n - (n-1))!) * (x - a)^(n - (n-1))).
      apply nth_derivative_imp_nth_derivative_on. apply differentiable_domain_open; lra.
      apply nth_derivative_pow_shift; lia.
    + intros k H6. admit.
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
        rewrite nth_derive_minus. do 2 f_equal. unfold Q. rewrite nth_derive_taylor_poly_const; auto.
        admit. admit.
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


Admitted.

Theorem theorem_20_2 : forall n a f, 
  nth_differentiable_at n f a ->
  (forall k, (1 <= k < n)%nat -> ⟦ Der ^ k a ⟧ f = 0) -> 
  ⟦ Der ^ n a ⟧ f <> 0 -> 
  ( (Nat.Even n /\ ⟦ Der ^ n a ⟧ f > 0 -> local_minimum_point f ℝ a) \/ 
    (Nat.Even n /\ ⟦ Der ^ n a ⟧ f < 0 -> local_maximum_point f ℝ a) \/
    (Nat.Odd n -> ~ local_maximum_point f ℝ a /\ ~ local_minimum_point f ℝ a) ).
Proof.
  intros n a f H1 H2 H3. admit.
Admitted.

Definition equal_up_to_order (n : nat) (f g : R -> R) (a : R) : Prop :=
  ⟦ lim a ⟧ (fun x => (f x - g x) / ((x - a) ^ n)) = 0.

Theorem theorem_20_3 : forall n a pl ql,
  let P := fun x => polynomial pl (x - a) in
  let Q := fun x => polynomial ql (x - a) in
  (length pl <= n + 1)%nat -> (length ql <= n + 1)%nat ->
  equal_up_to_order n P Q a ->
  P = Q.
Proof.
  intros n a pl ql P Q H1 H2 H3. admit.
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