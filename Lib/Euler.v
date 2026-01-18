From Lib Require Import Imports Notations Reals_util Functions Sums Sets Exponential
                        Limit Continuity Derivative Sequence Series.
Import SetNotations SumNotations FunctionNotations LimitNotations DerivativeNotations.

Open Scope R_scope.

Definition exp_series (x : R) : sequence :=
  fun k => x^k / (k!).

Definition exp_partial_sum (x : R) (n : nat) : R :=
  partial_sum (exp_series x) n.

Lemma exp_partial_sum_alt : forall x n,
  exp_partial_sum x n = ∑ 0 n (fun k => x^k / (k!)).
Proof.
  intros x n. unfold exp_partial_sum, partial_sum, exp_series. reflexivity.
Qed.

Lemma exp_series_converges : forall x,
  series_converges (exp_series x).
Proof.
  intros x.
  exists (exp x).
   
Admitted.

Definition E (x : R) : R :=  exp x.

Theorem exp_eq_series : forall x,
  exp x = E x.
Proof.
  intros x. unfold E. reflexivity.
Qed.

Corollary e_eq_series : e = E 1.
Proof.
  unfold e. apply exp_eq_series.
Qed.

Lemma E_0 : E 0 = 1.
Proof.
  unfold E. apply exp_0.
Qed.

Lemma E_1 : E 1 = e.
Proof.
  unfold E, e. reflexivity.
Qed.

Example exp_series_1_first_terms :
  map (exp_series 1) (seq 0 5) = [1; 1; 1/2; 1/6; 1/24].
Proof.
  unfold exp_series. simpl. 
  repeat (try rewrite pow_O; try rewrite pow_1; try rewrite pow_add).
  repeat rewrite fact_simpl.
  auto_list.
Qed.

Example exp_partial_sum_1_first_terms :
  map (exp_partial_sum 1) (seq 0 5) = [1; 2; 5/2; 8/3; 65/24].
Proof.
  unfold exp_partial_sum, partial_sum, exp_series.
  simpl.
Admitted.
