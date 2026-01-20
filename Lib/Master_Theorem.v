From Lib Require Import Imports Notations Reals_util Functions Sums Sets Sequence Exponential.

Open Scope R_scope.

Definition div_floor_R (n : nat) (b : R) : nat := 
  Z.to_nat (Int_part (INR n / b)).

Notation "⌊ n / b ⌋" := (div_floor_R n b) 
  (at level 9, n at level 30, b at level 30, format "⌊ n / b ⌋") : nat_scope.

Definition big_O (f g : ℕ -> ℝ) :=
  ∃ c N, c > 0 /\ ∀ (n : ℕ), n >= N -> |f n| <= c * |g n|.

Definition big_Omega (f g : ℕ -> ℝ) :=
  ∃ c N, c > 0 /\ ∀ (n : ℕ), n >= N -> |f n| >= c * |g n|.

Definition big_Theta (f g : ℕ -> ℝ) :=
  ∃ c1 c2 N, c1 > 0 /\ c2 > 0 /\ ∀ (n : ℕ), n >= N -> 
  c1 * |g n| <= |f n| <= c2 * |g n|.

Notation "u = Ο( v )" := (big_O u v) 
  (at level 70, no associativity, format "u  =  Ο( v )") : R_scope.

Notation "u = Ω( v )" := (big_Omega u v) 
  (at level 70, no associativity, format "u  =  Ω( v )") : R_scope.

Notation "u = Θ( v )" := (big_Theta u v) 
  (at level 70, no associativity, format "u  =  Θ( v )") : R_scope.

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