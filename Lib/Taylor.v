From Lib Require Import Imports Notations Reals_util Functions Sums Limit Continuity Derivative.
Import Function_Notations LimitNotations DerivativeNotations.

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

Theorem theorem_20_1 : forall n a f,
  nth_differentiable n f -> 
    ⟦ lim a ⟧ (λ x, (f x - P(n, a, f) x) / ((x - a)^n)) = 0.
Proof.

Admitted.

Theorem theorem_20_2 : forall n a f,
  (forall k, (1 <= k < n)%nat -> ⟦ Der^k a ⟧ f = 0) -> ⟦ Der^n a ⟧ f <> 0 ->
  (
    (Nat.Even n /\ ⟦ Der^n a ⟧ f > 0 -> local_minimum_point f ℝ a) /\
    (Nat.Even n /\ ⟦ Der^n a ⟧ f < 0 -> local_maximum_point f ℝ a) /\
    (Nat.Odd n -> ~ local_maximum_point f ℝ a /\ ~ local_minimum_point f ℝ a)
  ).
Proof.
  intros n a f H1 H2. split; [| split ]; intros H3.
  - destruct H3 as [H3 H4]. admit. 
  - destruct H3 as [H3 H4]. admit.
  - split; intros H4.
    -- admit.
    -- admit. 
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

Lemma Taylor_polynomial_is_polynomial : forall n a f,
  exists l, 
  let P := fun x => polynomial l (x - a) in
  (length l = n + 1)%nat /\
  P(n, a, f) = P.
Proof.
  intros n a f. admit.
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


