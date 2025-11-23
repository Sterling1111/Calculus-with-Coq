From Lib Require Import Imports.

Notation ℕ := nat.
Notation ℤ := Z.
Notation ℚ := Q.
Notation ℝ := R.

Notation "| x |" := (Rabs x) 
  (at level 200, x at level 0, format "| x |", no associativity) : R_scope.

Notation "√ x" := (sqrt x) (format "√ x", at level 20).

Open Scope R_scope.

Notation "l .[ i ]" := (nth i l 0)
  (at level 10, format "l .[ i ]").

(* Single-term Unicode (keep ASCII <=, >= as already provided by Coq/Reals) *)
Notation "x ≤ y" := (Rle x y) : R_scope.
Notation "x ≥ y" := (Rge x y) : R_scope.

(* --- Three-term chains --- *)
Notation "a <= b <= c" := (a <= b /\ b <= c)
  (at level 70, b at next level, c at next level) : R_scope.
Notation "a ≥ b ≥ c" := (a ≥ b /\ b ≥ c)
  (at level 70, b at next level, c at next level) : R_scope.
Notation "a ≤ b ≤ c" := (a ≤ b /\ b ≤ c)
  (at level 70, b at next level, c at next level) : R_scope.
Notation "a >= b >= c" := (a >= b /\ b >= c)
  (at level 70, b at next level, c at next level) : R_scope.

Notation "a < b < c" := (a < b /\ b < c)
  (at level 70, b at next level, c at next level) : R_scope.
Notation "a > b > c" := (a > b /\ b > c)
  (at level 70, b at next level, c at next level) : R_scope.

(* --- Four-term chains --- *)
Notation "a <= b <= c <= d" := (a <= b /\ b <= c /\ c <= d)
  (at level 70, b at next level, c at next level, d at next level) : R_scope.
Notation "a ≥ b ≥ c ≥ d" := (a ≥ b /\ b ≥ c /\ c ≥ d)
  (at level 70, b at next level, c at next level, d at next level) : R_scope.
Notation "a ≤ b ≤ c ≤ d" := (a ≤ b /\ b ≤ c /\ c ≤ d)
  (at level 70, b at next level, c at next level, d at next level) : R_scope.
Notation "a >= b >= c >= d" := (a >= b /\ b >= c /\ c >= d)
  (at level 70, b at next level, c at next level, d at next level) : R_scope.

Notation "a < b < c < d" := (a < b /\ b < c /\ c < d)
  (at level 70, b at next level, c at next level, d at next level) : R_scope.
Notation "a > b > c > d" := (a > b /\ b > c /\ c > d)
  (at level 70, b at next level, c at next level, d at next level) : R_scope.

(* --- Mixed four-term chains (your lemma needs this one) --- *)
Notation "a <= b < c <= d" := (a <= b /\ b < c /\ c <= d)
  (at level 70, b at next level, c at next level, d at next level) : R_scope.
Notation "a ≤ b < c ≤ d" := (a ≤ b /\ b < c /\ c ≤ d)
  (at level 70, b at next level, c at next level, d at next level) : R_scope.

(* Mirror mixed four-term (≥ with > in the middle) *)
Notation "a >= b > c >= d" := (a >= b /\ b > c /\ c >= d)
  (at level 70, b at next level, c at next level, d at next level) : R_scope.
Notation "a ≥ b > c ≥ d" := (a ≥ b /\ b > c /\ c ≥ d)
  (at level 70, b at next level, c at next level, d at next level) : R_scope.

(* --- Mixed five-term chains --- *)
Notation "a <= b < c < d <= e" := (a <= b /\ b < c /\ c < d /\ d <= e)
  (at level 70, b at next level, c at next level, d at next level, e at next level) : R_scope.
Notation "a ≤ b < c < d ≤ e" := (a ≤ b /\ b < c /\ c < d /\ d ≤ e)
  (at level 70, b at next level, c at next level, d at next level, e at next level) : R_scope.

(* Mirror mixed five-term *)
Notation "a >= b > c > d >= e" := (a >= b /\ b > c /\ c > d /\ d >= e)
  (at level 70, b at next level, c at next level, d at next level, e at next level) : R_scope.
Notation "a ≥ b > c > d ≥ e" := (a ≥ b /\ b > c /\ c > d /\ d ≥ e)
  (at level 70, b at next level, c at next level, d at next level, e at next level) : R_scope.

(* Optional: three-term mixed chains for completeness *)
Notation "a <= b < c" := (a <= b /\ b < c)
  (at level 70, b at next level, c at next level) : R_scope.
Notation "a ≤ b < c" := (a ≤ b /\ b < c)
  (at level 70, b at next level, c at next level) : R_scope.
Notation "a >= b > c" := (a >= b /\ b > c)
  (at level 70, b at next level, c at next level) : R_scope.
Notation "a ≥ b > c" := (a ≥ b /\ b > c)
  (at level 70, b at next level, c at next level) : R_scope.


Declare Scope interval_scope.
Delimit Scope interval_scope with interval.

Module IntervalNotations.
  Notation "[ a , b ]" := (fun x => a <= x <= b) : interval_scope.
  Notation "[ a , b ⦆" := (fun x => a <= x < b) : interval_scope.
  Notation "⦅ a , b ]" := (fun x => a < x <= b)  : interval_scope.
  Notation "⦅ a , b ⦆" := (fun x => a < x < b) : interval_scope.

  Notation "⦅-∞ , b ⦆" := (fun x => x < b) : interval_scope.
  Notation "⦅ -∞ , b ]" := (fun x => x <= b) : interval_scope.
  Notation "⦅ a , +∞]" := (fun x => a < x) : interval_scope.
  Notation "[ a , +∞⦆" := (fun x => a <= x) : interval_scope.

  Notation "⦅-∞ , +∞⦆" := (Full_set _) : interval_scope.

  Notation "( a , b )" := (fun x => a < x < b) : interval_scope.
  Notation "[ a , b )" := (fun x => a <= x < b) : interval_scope.
  Notation "( a , b ]" := (fun x => a < x <= b) : interval_scope.
End IntervalNotations.