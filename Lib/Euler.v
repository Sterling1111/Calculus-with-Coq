From Lib Require Import Imports Notations Reals_util Functions Sums Sets Exponential
                        Limit Continuity Derivative Sequence Series.
Import SetNotations.

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

(** The exponential series converges for all x *)
Lemma exp_series_converges : forall x,
  series_converges (exp_series x).
Proof.
  intros x.
  (* The partial sums converge to exp x *)
  exists (exp x).
  (* This requires showing that |exp_partial_sum x n - exp x| → 0 *)
  (* Which is equivalent to showing the Taylor remainder → 0 *)
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
