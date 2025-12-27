From Lib Require Import Imports Notations Reals_util Functions Sums Sets Limit Continuity Derivative Trigonometry.
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

Theorem theorem_20_1 : forall n a f D,
  (n > 0)%nat -> 
  interior_point D a ->
  nth_differentiable_on n f D -> 
  ⟦ lim a ⟧ (λ x, (f x - P(n, a, f) x) / ((x - a)^n)) = 0.
Proof.
  intros n a f D H1 H2 H3. 
  set (Q := λ x, ∑ 0 (n - 1) λ i, (⟦ Der^i a ⟧ f) / i! * (x - a) ^ i).
  set (g := λ x, (x - a)^n).
  apply limit_plus_constant with (C := ⟦ Der^n a ⟧ f / n!). rewrite Rplus_0_l.
  apply limit_to_a_equiv with (f1 := λ x, (f x - Q x) / g x).
  {
    intros x H4. unfold Q, Taylor_polynomial, g. replace n with (S (n - 1))%nat at 3 by lia.
    rewrite sum_f_i_Sn_f; try lia. replace (S (n - 1)) with n by lia. field. split. apply INR_fact_neq_0.
    apply pow_nonzero. lra.
  }

  assert (H4 : forall k, (k <= n - 1)%nat -> ⟦ Der^k a⟧ Q = ⟦ Der^k a⟧ f) by admit.
  assert (H5 : forall k, ⟦ Der^k ⟧ g = (λ x, n! * (x - a) ^ (n - k)/(n-k)!)) by admit.

  apply lhopital_nth_local with (D := D) (n := (n-1)%nat); auto.
  - admit.
  - admit.
  - intros k H6. admit.
  - intros k H6. admit.
  - replace (⟦ Der^(n - 1) ⟧ g D) with (fun x => n! * (x - a)).
    2: {
      extensionality x.
      specialize (H5 (n - 1)%nat). replace (λ x : ℝ, n! * (x - a) ^ (n - (n - 1)) / (n - (n - 1))!) with (λ x, n! * (x - a)) in H5.
      2 : { extensionality y. replace (n - (n - 1))%nat with 1%nat by lia. simpl. lra. }
      replace ((⟦ Der^(n - 1) ⟧ g D) x) with ((⟦ Der^(n - 1) ⟧ g) x).
      - rewrite H5. reflexivity.
      - admit.
  }
  replace (⟦ Der^(n - 1) ⟧ (f - Q) D) with ((⟦ Der^(n-1) ⟧ f - ⟦ Der^(n-1) ⟧ f))%f.
  2: {
    extensionality x.
    admit. 
  }
  admit.
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