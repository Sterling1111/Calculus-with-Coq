From Lib Require Import Imports Complex.

Notation ℕ := nat.
Notation ℤ := Z.
Notation ℚ := Q.
Notation ℝ := R.
Notation ℂ := C.

Notation "| x |" := (Rabs x)
  (at level 35, x at level 0, format "| x |", no associativity) : R_scope.

Notation "| c |" := (Cnorm c) 
  (at level 35, c at level 0, format "| c |", no associativity) : C_scope.

Notation "√ x" := (sqrt x) (format "√ x", at level 20).

Notation "n !" := (fact n) (format "n !", at level 10).

Definition Nfloor (x : R) : nat := Z.to_nat (Int_part x).
Definition Nceil (x : R) : nat := Z.to_nat (up x).

Notation "⌊ x ⌋" := (Nfloor x) (at level 9, format "⌊ x ⌋").
Notation "⌈ x ⌉" := (Nceil x) (at level 9, format "⌈ x ⌉").

Open Scope R_scope.

Notation "l .[ i ]" := (nth i l 0)
  (at level 10, format "l .[ i ]").

Notation "x = y = z" := (x = y /\ y = z)
  (at level 70, y at next level, z at next level) : type_scope.

Notation "x ≤ y" := (Rle x y) : R_scope.
Notation "x ≥ y" := (Rge x y) : R_scope.

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

Notation "a <= b < c <= d" := (a <= b /\ b < c /\ c <= d)
  (at level 70, b at next level, c at next level, d at next level) : R_scope.
Notation "a ≤ b < c ≤ d" := (a ≤ b /\ b < c /\ c ≤ d)
  (at level 70, b at next level, c at next level, d at next level) : R_scope.

Notation "a >= b > c >= d" := (a >= b /\ b > c /\ c >= d)
  (at level 70, b at next level, c at next level, d at next level) : R_scope.
Notation "a ≥ b > c ≥ d" := (a ≥ b /\ b > c /\ c ≥ d)
  (at level 70, b at next level, c at next level, d at next level) : R_scope.

Notation "a <= b < c < d <= e" := (a <= b /\ b < c /\ c < d /\ d <= e)
  (at level 70, b at next level, c at next level, d at next level, e at next level) : R_scope.
Notation "a ≤ b < c < d ≤ e" := (a ≤ b /\ b < c /\ c < d /\ d ≤ e)
  (at level 70, b at next level, c at next level, d at next level, e at next level) : R_scope.

Notation "a >= b > c > d >= e" := (a >= b /\ b > c /\ c > d /\ d >= e)
  (at level 70, b at next level, c at next level, d at next level, e at next level) : R_scope.
Notation "a ≥ b > c > d ≥ e" := (a ≥ b /\ b > c /\ c > d /\ d ≥ e)
  (at level 70, b at next level, c at next level, d at next level, e at next level) : R_scope.

Notation "a <= b < c" := (a <= b /\ b < c)
  (at level 70, b at next level, c at next level) : R_scope.
Notation "a ≤ b < c" := (a ≤ b /\ b < c)
  (at level 70, b at next level, c at next level) : R_scope.
Notation "a >= b > c" := (a >= b /\ b > c)
  (at level 70, b at next level, c at next level) : R_scope.
Notation "a ≥ b > c" := (a ≥ b /\ b > c)
  (at level 70, b at next level, c at next level) : R_scope.