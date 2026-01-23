From Lib Require Import Imports Notations Reals_util Functions Sums Sets Sequence Exponential.
Import SumNotations SequenceNotations FunctionNotations.

Open Scope R_scope.

Definition big_O (f g : ℕ -> ℝ) :=
  ∃ c N, c > 0 /\ ∀ (n : ℕ), n >= N -> |f n| <= c * |g n|.

Definition big_Omega (f g : ℕ -> ℝ) :=
  ∃ c N, c > 0 /\ ∀ (n : ℕ), n >= N -> |f n| >= c * |g n|.

Definition big_Theta (f g : ℕ -> ℝ) :=
  ∃ c1 c2 N, c1 > 0 /\ c2 > 0 /\ ∀ (n : ℕ), n >= N -> 
  c1 * |g n| <= |f n| <= c2 * |g n|.

Definition little_o (f g : ℕ -> ℝ) :=
  ∀ c, c > 0 -> ∃ N, ∀ (n : ℕ), n >= N -> |f n| <= c * |g n|.

Definition little_omega (f g : ℕ -> ℝ) :=
  ∀ c, c > 0 -> ∃ N, ∀ (n : ℕ), n >= N -> |f n| >= c * |g n|.

Notation "f = Ο( g )" := (big_O f g) 
  (at level 70, no associativity, format "f  =  Ο( g )") : R_scope.

Notation "f = Ω( g )" := (big_Omega f g) 
  (at level 70, no associativity, format "f  =  Ω( g )") : R_scope.

Notation "f = Θ( g )" := (big_Theta f g) 
  (at level 70, no associativity, format "f  =  Θ( g )") : R_scope.

Notation "f = o( g )" := (little_o f g) 
  (at level 70, no associativity, format "f  =  o( g )") : R_scope.

Notation "f = ω( g )" := (little_omega f g) 
  (at level 70, no associativity, format "f  =  ω( g )") : R_scope.

Lemma big_theta_iff (f g : ℕ -> ℝ) :
  f = Θ( g ) <-> (f = Ο( g ) /\ f = Ω( g )).
Proof.
  split.
  - intros [c1 [c2 [N [H1 [H2 H3]]]]]. split; 
    [exists c2, N | exists c1, N]; split; auto; intros n H4; 
    specialize (H3 n H4); lra.
  - intros [[c1 [N1 [H3 H4]]] [c2 [N2 [H5 H6]]]].
    set (N := Rmax N1 N2). exists c2, c1, N. split; [| split]; auto.
    intros n H7.
    specialize (H4 n ltac:(unfold N in *; solve_R)).
    specialize (H6 n ltac:(unfold N in *; solve_R)).
    lra.
Qed.

Lemma little_o_iff_limit_zero : forall f g,
  (forall n, g n <> 0) ->
  f = o(g) <-> ⟦ lim ⟧ (λ n, f n / g n) = 0.
Proof.
  intros f g H1. split.
  - intros H2 ε H3. specialize (H2 (ε/2) ltac:(lra)) as [N H4]. exists N. intros n H5.
    specialize (H4 n ltac:(solve_R)). rewrite Rminus_0_r. unfold Rdiv.
    rewrite Rabs_mult, Rabs_inv. specialize (H1 n).
    apply Rmult_lt_reg_r with (r := |g n|); [solve_R |].
    apply Rmult_le_compat_l with (r := 2) in H4; try lra.
    field_simplify in H4. field_simplify; solve_R.
  - intros H2 c H3. specialize (H2 (c/2) ltac:(lra)) as [N H4]. exists (N + 1). intros n H5.
    specialize (H4 n ltac:(solve_R)). rewrite Rminus_0_r in H4.
    unfold Rdiv in H4. rewrite Rabs_mult, Rabs_inv in H4.
    specialize (H1 n). apply Rmult_lt_compat_r with (r := |g n|) in H4; [| solve_R].
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r in H4; solve_R.
Qed.

Lemma little_omega_iff_limit_infty : forall f g,
  (forall n, g n <> 0) ->
  f = ω(g) <-> ⟦ lim ⟧ (λ n, |f n / g n|) = ∞.
Proof.
  intros f g H1. split.
  - intros H2 M. destruct (Rlt_dec M 0) as [H3 | H3].
    + exists 0%nat. solve_R.
    + specialize (H2 (M + 1) ltac:(lra)) as [N H4].
      exists N. intros n H5. specialize (H4 n ltac:(solve_R)).
      unfold Rdiv. rewrite Rabs_mult, Rabs_inv. specialize (H1 n).
      apply Rmult_lt_reg_r with (r := |g n|); [ solve_R |].
      rewrite Rmult_assoc, Rinv_l, Rmult_1_r; solve_R.
  - intros H2 c H3.
    specialize (H2 c) as [N H4].
    exists (N + 1). intros n H5. specialize (H4 n ltac:(solve_R)).
    unfold Rdiv in H4. rewrite Rabs_mult, Rabs_inv in H4.
    apply Rmult_lt_compat_r with (r := |g n|) in H4; [| apply Rabs_pos_lt; apply H1].
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r in H4; solve_R.
Qed.
    
Theorem big_theta_trans : forall f g h,
  f = Θ( g ) -> g = Θ( h ) -> f = Θ( h ).
Proof.
  intros f g h [c1 [c2 [N1 [H1 [H2 H3]]]]] [d1 [d2 [N2 [H4 [H5 H6]]]]].
  set (N := Rmax N1 N2). exists (c1 * d1), (c2 * d2), N.
  split; [| split]; try nra.
  intros n H7. 
  specialize (H3 n ltac:(unfold N in *; solve_R)).
  specialize (H6 n ltac:(unfold N in *; solve_R)).
  nra.
Qed.

Theorem big_O_trans : forall f g h,
  f = Ο( g ) -> g = Ο( h ) -> f = Ο( h ).
Proof.
  intros f g h [c1 [N1 [H1 H2]]] [c2 [N2 [H3 H4]]].
  set (N := Rmax N1 N2). exists (c1 * c2), N.
  split; [nra |].
  intros n H5.
  specialize (H2 n ltac:(unfold N in *; solve_R)).
  specialize (H4 n ltac:(unfold N in *; solve_R)).
  nra.
Qed.

Theorem big_Omega_trans : forall f g h,
  f = Ω( g ) -> g = Ω( h ) -> f = Ω( h ).
Proof.
  intros f g h [c1 [N1 [H1 H2]]] [c2 [N2 [H3 H4]]].
  set (N := Rmax N1 N2). exists (c1 * c2), N.
  split; [nra |].
  intros n H5.
  specialize (H2 n ltac:(unfold N in *; solve_R)).
  specialize (H4 n ltac:(unfold N in *; solve_R)).
  nra.
Qed.

Theorem little_o_trans : forall f g h,
  f = o( g ) -> g = o( h ) -> f = o( h ).
Proof.
  intros f g h H1 H2 c H3.
  specialize (H1 c H3) as [N1 H4].
  specialize (H2 1 ltac:(lra)) as [N2 H5].
  set (N := Rmax N1 N2). exists N.
  intros n H6.
  specialize (H4 n ltac:(unfold N in *; solve_R)).
  specialize (H5 n ltac:(unfold N in *; solve_R)).
  nra.
Qed.

Theorem little_omega_trans : forall f g h,
  f = ω( g ) -> g = ω( h ) -> f = ω( h ).
Proof.
  intros f g h H1 H2 c H3.
  specialize (H1 c H3) as [N1 H4].
  specialize (H2 1 ltac:(lra)) as [N2 H5].
  set (N := Rmax N1 N2). exists N.
  intros n H6.
  specialize (H4 n ltac:(unfold N in *; solve_R)).
  specialize (H5 n ltac:(unfold N in *; solve_R)).
  nra.
Qed.

Theorem big_theta_refl : forall f, f = Θ( f ).
Proof.
  intros f. exists 1, 1, 0%nat. repeat split; lra.
Qed.

Theorem big_O_refl : forall f, f = Ο( f ).
Proof.
  intros f. exists 1, 0%nat. split; solve_R.
Qed.

Lemma big_Omega_refl : forall f, f = Ω( f ).
Proof.
  intros f. exists 1, 0%nat. split; solve_R.
Qed.

Theorem big_theta_sym : forall f g,
  f = Θ( g ) <-> g = Θ( f ).
Proof.
  intros f g. split; intros H1.
  - destruct H1 as [c1 [c2 [N [H2 [H3 H4]]]]].
    exists (1 / c2), (1 / c1), N. split; [| split]; try (apply Rdiv_pos_pos; lra).
    intros n H5. specialize (H4 n H5). split.
    + apply Rmult_le_reg_r with (r := c2); try lra. field_simplify; solve_R.
    + apply Rmult_le_reg_r with (r := c1); try lra. field_simplify; solve_R.
  - destruct H1 as [c1 [c2 [N [H2 [H3 H4]]]]].
    exists (1 / c2), (1 / c1), N. split; [| split]; try (apply Rdiv_pos_pos; lra).
    intros n H5. specialize (H4 n H5). split.
    + apply Rmult_le_reg_r with (r := c2); try lra. field_simplify; solve_R.
    + apply Rmult_le_reg_r with (r := c1); try lra. field_simplify; solve_R.
Qed.

Theorem transpose_sym_O_Omega : forall f g,
  f = Ο( g ) <-> g = Ω( f ).
Proof.
  intros f g. split; intros H1.
  - destruct H1 as [c [N [H2 H3]]]. 
    exists (1 / c), N. split; try (apply Rdiv_pos_pos; lra).
    intros n H4. specialize (H3 n H4). apply Rle_ge.
    apply Rmult_le_reg_r with (r := c); try lra. field_simplify; solve_R.
  - destruct H1 as [c [N [H2 H3]]].
    exists (1 / c), N. split; try (apply Rdiv_pos_pos; lra).
    intros n H4. specialize (H3 n H4).
    apply Rmult_le_reg_r with (r := c); try lra. field_simplify; solve_R.
Qed.

Theorem transpose_sym_o_omega : forall f g,
  f = o( g ) <-> g = ω( f ).
Proof.
  intros f g. split; intros H1.
  - intros c H2. specialize (H1 (1 / c) ltac:(apply Rdiv_pos_pos; lra)) as [N H3].
    exists N. intros n H4. specialize (H3 n H4). apply Rle_ge.
    apply Rmult_le_compat_l with (r := c) in H3; try lra.
    field_simplify in H3; solve_R.
  - intros c H2. specialize (H1 (1 / c) ltac:(apply Rdiv_pos_pos; lra)) as [N H3].
    exists N. intros n H4. specialize (H3 n H4). apply Rge_le in H3.
    apply Rmult_le_compat_l with (r := c) in H3; try lra.
    field_simplify in H3; solve_R.
Qed.

Lemma big_O_extend_1 : forall (f : nat -> R) (g : nat -> R) (N : R) (c : R),
  (forall n, (n >= 1)%nat -> g n > 0) ->
  (forall n : nat, n >= N -> f n <= c * g n) ->
  exists c', forall n, (n >= 1)%nat -> f n <= c' * g n.
Proof.
  intros f g N c H1 H2.
  set (k := Z.to_nat (up N)).
  assert (H3: exists x, forall n, (1 <= n <= k)%nat -> f n <= x * g n).
  { induction k as [|k [x H3]].
    - exists 0; intros n H3; lia.
    - exists (Rmax x (f (S k) / g (S k))); intros n H4.
      destruct (eq_nat_dec n (S k)) as [H5|H5].
      + rewrite H5; apply Rle_trans with ((f (S k) / g (S k)) * g (S k)); [|apply Rmult_le_compat_r; [apply Rlt_le, H1; lia|apply Rmax_r]].
        right; field. specialize (H1 (S k) ltac:(solve_R)). solve_R.
      + apply Rle_trans with (x * g n); [apply H3; lia|].
        apply Rmult_le_compat_r; [apply Rlt_le, H1; lia|apply Rmax_l]. }
  destruct H3 as [x H3]; exists (Rmax c x); intros n H4.
  destruct (le_gt_dec n k) as [H5|H5].
  - apply Rle_trans with (x * g n); [apply H3; lia|].
    apply Rmult_le_compat_r; [apply Rlt_le, H1; lia|apply Rmax_r].
  - apply Rle_trans with (c * g n); [apply H2|apply Rmult_le_compat_r; [apply Rlt_le, H1; lia|apply Rmax_l]].
    apply Rle_ge, Rlt_le, Rlt_le_trans with (IZR (up N)); [apply archimed | rewrite INR_IZR_INZ; apply IZR_le; lia].
Qed.

Lemma floor_power_bound : forall p : R, 
  exists k : R, k > 0 /\ forall x : R, x >= 1 -> ⌊x⌋^^p <= k * x^^p.
Proof.
  intro p. destruct (Rle_dec 0 p) as [H1|H1].
  - exists 1; split; [lra |].
    intros x H2. rewrite Rmult_1_l.
    apply Rpower_le; pose proof floor_spec x ltac:(lra); lra.
  - exists (2 ^^ (-p)); split; [apply Rpower_gt_0; lra |].
    intros x H2.
    assert (H3 : 0 < -p) by (apply Rlt_0_minus ; lra).
    assert (H4 : x <= 2 * ⌊x⌋).
    {
      pose proof floor_spec x ltac:(lra) as [H4 H5].
      destruct (⌊x⌋). simpl in *; try nra. rewrite S_INR in *.
      pose proof pos_INR n; lra.
    }
replace (2 ^^ (- p) * x ^^ p) with ((x / 2) ^^ p).
2: {
  rewrite <- Rpower_inv; [| lra].
  rewrite <- Rpower_mult_distr; try lra.
  f_equal; lra.
}
apply Rpower_le_contravar; try lra.
Qed.

Section Master_Theorem.
  Variables (a b : ℝ) (f T T' : ℕ -> ℝ).

  Hypothesis H1 : a >= 1.
  Hypothesis H2 : b > 1.
  Hypothesis H3 : ∀ n, f n >= 0.
  Hypothesis H4 : ∀ n, T n >= 0.
  Hypothesis H5 : ∃ n, T n > 0.
  Hypothesis H6 : ∀ n : ℕ, n >= b -> T n = a * T (⌊n/b⌋) + f n.
  Hypothesis H7 : ∀ k : ℕ, T' k = T (⌊b^k⌋).

  Lemma lemma_4_2 : ∀ n : ℕ, (n > 0)%nat -> is_natural b ->
     T' n = a ^ n * T' 0 + ∑ 0 (n-1) (λ j, a ^ j * f (⌊b^(n-j)⌋)).
  Proof.
    intros n H8 H9. induction n as [| k IH]; try lia.
    assert ((k = 0)%nat \/ (k > 0)%nat) as [H10 | H10] by lia.
    - rewrite H10. sum_simpl. rewrite Rmult_1_r, H7, H7, pow_1, pow_O.
      pose proof floor_INR b H9 as H11. rewrite H6, H11, Rdiv_diag; lra.
    - replace (S k - 1)%nat with k by lia.
      rewrite H7, H6. 2 : { apply floor_power_succ_ge_base; auto. }
      rewrite floor_INR. 2 : { apply is_natural_pow; auto. }
      rewrite floor_power_succ_div; auto.
      rewrite <- H7, IH; auto.
      rewrite Rmult_plus_distr_l, <- Rmult_assoc, tech_pow_Rmult, r_mult_sum_f_i_n_f_l, Rplus_assoc.
      apply f_equal.
      rewrite (sum_f_split 0 0 k); try lia. rewrite sum_f_0_0, pow_O, Rmult_1_l, Nat.sub_0_r.
      rewrite (sum_f_reindex _ 1 k 1); try lia. rewrite Nat.sub_diag.
      rewrite Rplus_comm. apply f_equal.
      apply sum_f_equiv; try lia.
      intros j H11. replace (S k - (j + 1))%nat with (k - j)%nat by lia.
      replace (j + 1)%nat with (S j) by lia.
      rewrite <- Rmult_assoc, tech_pow_Rmult. reflexivity.
  Qed.

  Lemma lemma_4_2' : ∀ k : ℕ, (k > 0)%nat -> is_natural b ->
    let n := ⌊b ^ k⌋ in
    T n = n ^^ (log_ b a) * T 1 + 
          ∑ 0 (k - 1) (λ j, a ^ j * f (⌊n/b^j⌋)).
  Proof.
    intros k H8 H9 n. unfold n. rewrite <- H7.
    rewrite lemma_4_2; auto.
    fold n.
    replace (T' 0) with (T 1).
    2 : { rewrite H7, pow_O. replace 1 with (INR 1) by auto. rewrite floor_INR_id; auto. }
    f_equal.
    - unfold n. rewrite floor_INR. 2 : { apply is_natural_pow; auto. }
      rewrite power_base_change with (b := b); lra.
    - apply sum_f_equiv; try lia.
      intros j H10. unfold n.
      rewrite floor_INR. 2 : { apply is_natural_pow; auto. }
      rewrite <- pow_div_sub; solve_R.
  Qed.

  Lemma lemma_4_3 :
    let g := λ k, ∑ 0 (k - 1) (λ j, a ^ j * f (⌊b^(k-j)⌋)) in
    ((∃ ε, ε > 0 /\ f = Ο(λ n, n ^^ (log_ b a - ε))) -> 
      g = Ο(λ k, (b^k) ^^ (log_ b a))) /\
    (f = Θ(λ n, n ^^ (log_ b a)) -> 
      g = Θ(λ k, (b^k) ^^ (log_ b a) * k)) /\
    ((∃ ε c N, ε > 0 /\ c < 1 /\ f = Ω(λ n, n ^^ (log_ b a + ε)) /\ 
      (∀ n : ℕ, n >= N -> a * f (⌊n/b⌋) <= c * f n)) -> 
      g = Θ(λ k, f (⌊b^k⌋))).
  Proof.
    intros g. split; [| split].
    - intros [ε [H10 [c [N [H12 H13]]]]]. 
      set (q := b ^^ ε).
      assert (H14 : q > 1). { unfold q. apply Rpower_gt_1; try lra. }

      set (h := λ n : nat, n ^^ (log_ b a - ε)).

      assert (exists c', ∀ n, (n >= 1)%nat -> |f n| <= c' * |h n|) as [c' H15].
      {
        apply big_O_extend_1 with (N := N) (c := c); auto.
        intros n H15. unfold h. apply Rabs_pos_lt, Rgt_not_eq, Rpower_gt_0; solve_R.
      }

      pose proof floor_power_bound (log_ b a - ε) as [j [H16 H17]].

      set (c'' := Rmax 1 (c' * j)).

      assert (H18 : c'' > 0). { unfold c''. solve_R. }
      
      exists (c'' * q / (q - 1)), 1. split; [apply Rdiv_pos_pos; nra |].
      intros n H19. unfold g. 
      rewrite Rabs_right.
      2 : {
        apply Rle_ge. apply sum_f_nonneg; try lia. intros k H20.
        specialize (H3 (⌊b^(n - k)⌋)). pose proof pow_lt a k ltac:(lra) as H21. nra.
      }

      apply Rle_trans with (r2 := ∑ 0 (n - 1) (λ k, a ^ k * (c'' * (b ^ (n - k)) ^^ (log_ b a - ε)))).
      {
        apply sum_f_congruence_le; try lia.
        intros k H20. 
        apply Rmult_le_compat_l; [apply pow_le; lra |].

        assert (H21 : (⌊b ^ (n - k)⌋ >= 1)%nat).
        {
          assert (H21 : b ^ (n - k) >= 1).
          { apply Rle_ge. apply pow_R1_Rle; lra. }
          pose proof floor_spec (b ^ (n - k)) ltac:(lra) as [H22 H23].
          destruct (⌊b ^ (n - k)⌋); simpl in *; solve_R.
        }

        specialize (H15 (⌊b^(n - k)⌋) H21). 
        rewrite Rabs_right in H15; auto.
        rewrite Rabs_right in H15; [ | apply Rpower_ge_0 ].
        apply Rle_trans with (c' * h ⌊b ^ (n - k)⌋); auto.
        unfold h.
        assert (H22: 0 <= c').
        { 
          apply Rmult_le_reg_r with (⌊b ^ (n - k)⌋ ^^ (log_ b a - ε)).
          - apply Rpower_gt_0. solve_R.
          - rewrite Rmult_0_l. apply Rle_trans with (f ⌊b ^ (n - k)⌋); auto.
            apply Rge_le. apply H3.
        }
        apply Rle_trans with (c' * (j * (b ^ (n - k)) ^^ (log_ b a - ε))).
        + apply Rmult_le_compat_l; auto.
          apply H17. apply Rle_ge; apply pow_R1_Rle; lra.
        + rewrite <- Rmult_assoc.
          apply Rmult_le_compat_r.
          * apply Rge_le; apply Rpower_ge_0.
          * apply Rmax_r.
      }

      apply Rle_trans with (c'' * a ^ n * ∑ 0 (n - 1) (fun k => (1/q)^(n-k))).
      {
        replace (λ k : ℕ, a ^ k * (c'' * (b ^ (n - k))^^(log_ b a - ε))) with
                (λ k : ℕ, c'' * (a^k * (b ^ (n - k))^^(log_ b a - ε))) by (extensionality x; lra).
        rewrite <- r_mult_sum_f_i_n_f_l.
        right. rewrite Rmult_assoc. f_equal.
        rewrite r_mult_sum_f_i_n_f_l. 
        apply sum_f_equiv; [lia |].
        intros k H20.
        repeat rewrite <- Rpower_nat; try lra. 2 : { apply Rdiv_pos_pos; lra. }
        rewrite Rpower_mult; try lra.
        rewrite Rmult_minus_distr_l. unfold Rminus at 1. rewrite Rpower_plus; try lra.

        replace (b ^^ (INR (n - k) * log_ b a)) with (a ^^ INR (n - k)).
        2: {
          rewrite Rmult_comm.
          rewrite <- Rpower_mult; [| lra].
          unfold log_. f_equal. unfold Rpower. destruct (Rlt_dec 0 b); [| lra].
          replace (log a / log b * log b) with (log a).
          - rewrite exp_log; lra.
          - field. apply Rgt_not_eq. apply log_pos; lra.
        }
        rewrite <- Rmult_assoc.
        rewrite <- Rpower_plus; [| lra].
        replace (INR k + INR (n - k)) with (INR n) by (rewrite minus_INR; [lra | lia]).
        f_equal.
        unfold q.
        rewrite Rpower_inv; [| apply Rpower_gt_0; lra].
        rewrite Rpower_mult; [| lra].
        f_equal.
        lra.
      }

      replace (| (b ^ n) ^^ log_ b a |) with (a ^ n).
      2: { rewrite Rabs_right. apply power_base_change; try lra. apply Rpower_ge_0; lra. }
      rewrite Rmult_assoc. replace (c'' * q / (q - 1) * a ^ n) with (c'' * (a ^ n * (q / (q - 1)))) by nra.
      apply Rmult_le_compat_l; try lra. apply Rmult_le_compat_l. apply pow_le; lra.
      rewrite sum_f_geometric_rev.
      2 : { apply Rlt_not_eq. apply Rdiv_lt_1; lra. }
      2 : { apply INR_le. replace (INR 1) with 1 by auto. lra. }
      replace (q / (q - 1)) with (1 / (1 - 1 / q)).
      2: { field. split; lra. }
      apply Rmult_le_compat_r.
      + apply Rlt_le. apply Rinv_0_lt_compat. apply Rmult_lt_reg_r with (r := q); field_simplify; nra.
      + apply Rle_trans with (1 / q).
        * rewrite Rmult_minus_distr_l.
          rewrite Rmult_1_r.
          assert (0 <= 1 / q * (1 / q) ^ n).
          { apply Rmult_le_pos. pose proof Rdiv_pos_pos 1 q; lra. apply pow_le. pose proof Rdiv_pos_pos 1 q; lra. }
          lra.
        * apply Rlt_le. apply Rdiv_lt_1; lra.
    - admit.
    - admit.
  Admitted.

  Lemma lemma_4_4 :
    let p := log_ b a in
    is_natural b ->
    ((∃ ε, ε > 0 /\ (f = Ο(λ n, n^^(p - ε)))) -> T' = Θ(λ k, (b^k)^^p)) /\
    (f = Θ(λ n, n^^p) -> T' = Θ(λ k, (b^k)^^p * k)) /\
    ((∃ ε c N, ε > 0 /\ c < 1 /\ (f = Ω(λ n, n^^(p + ε))) /\ 
     (∀ n : ℕ, n >= N -> a * f (⌊n/b⌋) <= c * f n)) -> T' = Θ(λ k, f (⌊b^k⌋))).
  Proof.
    intros p H8. 
    set (g := λ k, ∑ 0 (k - 1) (λ j, a ^ j * f (⌊b^(k-j)⌋))).
    pose proof lemma_4_3 as [H9 [H10 H11]].
    fold g in H9, H10, H11.
    pose proof lemma_4_2 as H12.
    split; [| split].
    - intros [ε [H13 H14]]. specialize (H9 (ex_intro _ ε (conj H13 H14))).
apply big_theta_iff; split.
+ apply big_O_trans with (λ k, (b ^ k) ^^ p + g k).
  * exists 1, 1%nat. split; [lra |]. intros n H15.
    rewrite Rmult_1_l. rewrite Rabs_right. 2 : { rewrite H7, H4; lra. }
    rewrite H12; auto; [ | apply Rge_le, INR_le in H15; lia].
    rewrite Rabs_right. 
    2 : {
      apply Rle_ge, Rplus_le_le_0_compat.
      - apply Rge_le. apply Rpower_ge_0.
      - apply sum_f_nonneg; try lia. intros k H16. pose proof H3 (⌊b^(n - k)⌋) as H17. pose proof pow_lt a k ltac:(lra) as H18. nra.
    }
    replace ((b ^ n) ^^ p) with (a ^ n).
    2 : { unfold p. rewrite power_base_change with (b := b); lra. }j
    apply Rplus_le_compat.
    apply Rplus_le_compat_r.

    unfold p. rewrite power_base_change; try lra.
    rewrite Rmult_comm.
    destruct (Rle_dec (T' 0) 1).
    * apply Rmult_le_compat_l; [apply pow_le; lra | auto].
    * apply Rle_trans with (T' 0 * a ^ n).
      -- apply Rmult_le_compat_l; [apply pow_le; lra | lra].
      -- apply Rle_trans with (T' 0 * a ^ n + T' 0 * g n).
         ++ rewrite Rmult_plus_distr_l. apply Rplus_le_compat_l.
            apply Rmult_le_pos; [lra | apply sum_f_nonneg; try lia; intros; apply Rmult_le_pos; [apply pow_le; lra | apply H3]].
         ++ admit. (* Constant factor absorption *)
  + apply big_O_add.
    * apply big_O_mult_const. apply big_O_refl.
    * exact H9.
- apply big_Omega_trans with (λ k, (b ^ k) ^^ p).
  + apply big_Omega_refl.
  + exists (T' 0), 1%nat. split; [admit |]. (* Assume T' 0 > 0 *)
    intros n H15.
    rewrite H12; auto; [| lia].
    rewrite Rabs_right; [| apply H4].
    rewrite Rabs_right; [| apply Rpower_ge_0].
    apply Rle_trans with (a ^ n * T' 0).
    * apply Rmult_le_compat_r; [admit |].
      unfold p. rewrite power_base_change; try lra. lra.
    * apply Rle_trans with (a ^ n * T' 0 + g n); [| lra].
      rewrite Rplus_comm. apply Rle_trans with (g n + 0); [rewrite Rplus_0_r; lra |].
      apply Rplus_le_compat_l.
      apply sum_f_nonneg; try lia.
      intros j H16. apply Rmult_le_pos; [apply pow_le; lra | apply H3].

End Master_Theorem.

Theorem master_theorem : ∀ (a b : ℝ) (f T : ℕ -> ℝ),
  a >= 1 -> b > 1 ->
  (∀ n, f n >= 0) ->
  (∀ n, T n >= 0) -> 
  (∃ n, T n > 0) ->
  (∀ n : ℕ, n >= b -> T n = a * T (⌊n/b⌋) + f n) ->
  ((∃ ε, ε > 0 /\ (f = Ο(λ n, n^^((log_ b a) - ε)))) -> T = Θ(λ n, n^^(log_ b a))) /\
  (f = Θ(λ n, n^^(log_ b a)) -> T = Θ(λ n, n^^(log_ b a) * lg n)) /\
  ((∃ ε c N, ε > 0 /\ c < 1 /\ (f = Ω(λ n, n^^((log_ b a) + ε))) /\ 
   (∀ n : ℕ, n >= N -> a * f (⌊n/b⌋) <= c * f n)) -> T = Θ(f)).
Proof.
  intros a b f T H1 H2 H3 H4 H5 H6. split; [| split].
  - intros [ε [H7 H8]]. admit.
  - intros H7. admit.
  - intros [ε [c [N [H7 [H8 [H9 H10]]]]]]. admit.
Admitted.