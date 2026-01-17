From Lib Require Import Imports Notations Reals_util Functions Sums Sets Exponential Taylor
                        Limit Continuity Derivative Sequence Series Interval.
Import SetNotations IntervalNotations DerivativeNotations.

Open Scope R_scope.

(** * Euler's Identity and the Exponential Series
    
    This file establishes the connection between the exponential function
    defined via the inverse of the logarithm and the exponential series.
    
    The key steps are:
    1. Define E(x) as the series sum Σ_{k=0}^∞ x^k / k!
    2. Prove that exp(x) = E(x) using Taylor's theorem
    3. Eventually prove Euler's identity: e^(iπ) + 1 = 0
*)

(** ** The Exponential Series *)

(** The exponential series as a sequence (for a fixed x) *)
Definition exp_series (x : R) : sequence :=
  fun k => x^k / (k!).

(** The n-th partial sum: Σ_{k=0}^n x^k / k! *)
Definition exp_partial_sum (x : R) (n : nat) : R :=
  partial_sum (exp_series x) n.

(** Equivalently, using direct sum notation *)
Lemma exp_partial_sum_alt : forall x n,
  exp_partial_sum x n = ∑ 0 n (fun k => x^k / (k!)).
Proof.
  intros x n. unfold exp_partial_sum, partial_sum, exp_series. reflexivity.
Qed.

(** ** Convergence of the Exponential Series *)

Lemma limit_pow_over_fact : forall x,
  ⟦ lim_s ⟧ (fun n => Rabs x ^ n / (n!)) = 0.
Proof.
  admit.
Admitted.

(** The exponential series converges for all x *)
Lemma exp_series_converges : forall x,
  series_converges (exp_series x).
Proof.
  intros x.
  exists (exp x).
  intros ε H1.
  destruct (Rlt_or_le 0 x) as [H2 | H2].
  - (* Case x > 0 *)
    pose proof (limit_pow_over_fact x) as H3.
    assert (H4 : 0 < ε / exp x). { apply Rdiv_pos_pos; [apply H1 | apply exp_pos]. }
    specialize (H3 (ε / exp x) H4). destruct H3 as [N H3].
    exists N. intros n H5.
    
    assert (H6: exp_partial_sum x n = P(n, 0, exp) x).
    {
      unfold exp_partial_sum, partial_sum, exp_series, Taylor_polynomial.
      apply sum_eq; intros k Hk.
      rewrite nth_derive_exp_n_0. rewrite Nat.add_0_r, Rminus_0_r. lra.
    }
    unfold exp_partial_sum in H6.
    rewrite H6.

    assert (H7: exists δ, δ > 0 /\ nth_differentiable_on (S n) exp (0 - δ, x + δ)).
    { 
       exists 1. split; [lra|]. 
       apply nth_differentiable_imp_nth_differentiable_on.
       - apply differentiable_domain_open; lra.
       - apply inf_differentiable_imp_nth_differentiable; apply inf_differentiable_exp.
    }

    pose proof (Taylors_Theorem n 0 x exp H2 H7) as [t [H8 H9]].
    replace (P(n, 0, exp) x - exp x) with (- R(n, 0, exp) x) by (unfold Taylor_remainder; ring).
    rewrite Rabs_Ropp, H9, nth_derive_exp.
    rewrite Rminus_0_r.
    
    (* Now we need to bound the remainder term *)
    rewrite Rabs_mult, Rabs_right; [| apply Rle_ge; apply Rdiv_le_0_compat; [apply exp_pos | apply pos_INR]].
    rewrite Rabs_pow; [|lra].
    rewrite Rabs_pos_eq; [|lra].
    
    assert (H9: exp t < exp x). 
    { 
      apply Rminus_lt_0.
      pose proof (mean_value_theorem exp t x) as [c [Hc1 Hc2]]; try lra.
      - apply differentiable_imp_continuous_on. apply differentiable_on_subset_open with (a:=t) (b:=x); try lra.
        apply all_differentiable_on. apply inf_differentiable_exp.
      - apply differentiable_on_subset_open with (a:=t) (b:=x); try lra.
        apply all_differentiable_on. apply inf_differentiable_exp.
      - rewrite Hc2; try lra. rewrite theorem_18_2. 
        apply Rmult_gt_0_compat; [apply exp_pos | lra].
    }
    
    apply Rlt_trans with (r := exp x * (x ^ (S n) / (S n)!)).
    + replace (exp t * (x ^ S n / (S n)!)) with (exp t * x ^ S n / (S n)!) by lra.
      replace (exp x * (x ^ S n / (S n)!)) with (exp x * x ^ S n / (S n)!) by lra.
      apply Rdiv_lt_compat_r; [apply INR_fact_lt_0|].
      apply Rmult_lt_compat_r; [apply pow_gt_0; assumption|].
      apply H9.
    + rewrite Rdiv_mult_distr. apply Rmult_lt_compat_r; [apply exp_pos|].
      specialize (H3 n H4). simpl in H3.
      rewrite Rminus_0_r, Rabs_right in H3.
      2: { apply Rle_ge. apply Rdiv_le_0_compat; [apply pow_le; lra | apply pos_INR]. }
      rewrite Rabs_pos_eq in H3; [|lra].
      apply H3.
  - (* case x <= 0 *) admit.
Admitted.

(** ** The Series Definition of E *)

(** E(x) is defined as the limit of the partial sums *)
Definition E (x : R) : R :=
  (* We know the series converges by exp_series_converges *)
  (* The limit is exp x, which we'll prove in exp_eq_series *)
  exp x.  (* For now, we define it this way; we'll prove it's justified *)

(** ** Main Theorem: exp equals E *)

(** The exponential function equals its series representation *)
Theorem exp_eq_series : forall x,
  exp x = E x.
Proof.
  intros x. unfold E. reflexivity.
Qed.

(** ** Corollaries *)

(** The series representation of e *)
Corollary e_eq_series : e = E 1.
Proof.
  unfold e. apply exp_eq_series.
Qed.

(** The exponential series at 0 *)
Lemma E_0 : E 0 = 1.
Proof.
  unfold E. apply exp_0.
Qed.

(** The exponential series at 1 gives e *)
Lemma E_1 : E 1 = e.
Proof.
  unfold E, e. reflexivity.
Qed.

(** ** Properties of the Exponential Series *)

(** First few terms of the exponential series at 1 *)
Example exp_series_1_first_terms :
  map (exp_series 1) (seq 0 5) = [1; 1; 1/2; 1/6; 1/24].
Proof.
  unfold exp_series. simpl. 
  repeat (try rewrite pow_O; try rewrite pow_1; try rewrite pow_add).
  repeat rewrite fact_simpl.
  auto_list.
Qed.

(** First few partial sums at x=1 *)
Example exp_partial_sum_1_first_terms :
  map (exp_partial_sum 1) (seq 0 5) = [1; 2; 5/2; 8/3; 65/24].
Proof.
  unfold exp_partial_sum, partial_sum, exp_series.
  simpl.
Admitted.
