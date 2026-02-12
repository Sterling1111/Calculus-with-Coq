From Lib Require Import Imports Sets Functions Notations Sums WI_SI_WO.
Import SetNotations.

Notation subType := SetNotations.subType.

Open Scope R_scope.

Definition n_N (n : nat) : Type := subType (fun x : nat => exists k : nat, (x = n * k)%nat).

Notation "n 'N'" := (n_N n) (at level 0, format "n 'N'").

Open Scope Z_scope.

Lemma Nat_even_false_Odd : forall n, Nat.even n = false -> exists k, n = (2 * k + 1)%nat.
Proof.
  intros n H1. apply Nat.odd_spec.
  rewrite <- Nat.negb_even, H1. trivial.
Qed.

Theorem theorem_29_4 : ‖ ℕ ‖ = ‖ ℤ ‖.
Proof.
  apply eq_cardinality_Type.
  set (f := fun n : nat => if Nat.even n then Z.of_nat (n / 2) else - Z.of_nat (n / 2 + 1)). left. split.
  exists f. split.
  - intros x y H1. unfold f in H1. destruct (Nat.even x) eqn:H2, (Nat.even y) eqn:H3.
    -- apply Nat.even_spec in H2 as [j H2], H3 as [k H3]; subst. apply Nat2Z.inj in H1.
       do 2 (rewrite Nat.mul_comm, Nat.div_mul in H1; try lia).
    -- pose proof Zle_0_nat (x / 2) as H4. pose proof Zle_0_nat (y / 2 + 1) as H5. lia.
    -- pose proof Zle_0_nat (x / 2 + 1) as H4. pose proof Zle_0_nat (y / 2) as H5. lia.
    -- apply Z.opp_inj in H1. apply Nat_even_false_Odd in H2 as [j H2], H3 as [k H3]; subst.
       apply Nat2Z.inj in H1. rewrite Nat.mul_comm in H1. rewrite Nat.mul_comm with (n := 2%nat) in H1.
       rewrite Nat.div_add_l in H1; try lia. rewrite Nat.div_add_l in H1; try lia.
  - intros y. assert (y >= 0 \/ y < 0) as [H1 | H1] by lia.
    -- exists (2 * Z.to_nat y)%nat. unfold f. destruct (Nat.even (2 * Z.to_nat y)) eqn:H2.
       * rewrite Nat.mul_comm. rewrite Nat.div_mul; try lia.
       * apply Nat_even_false_Odd in H2 as [j H2]. lia.
    -- exists (2 * Z.to_nat (- y) - 1)%nat. unfold f. destruct (Nat.even (2 * Z.to_nat (- y) + 1)) eqn:H2.
       * apply Nat.even_spec in H2 as [j H2]. lia.
       * destruct (Nat.even (2 * Z.to_nat (- y) - 1)) eqn:H3.
         + apply Nat.even_spec in H3 as [j H3]. lia.
         + apply Nat_even_false_Odd in H3 as [j H3]. rewrite H3. rewrite Nat.mul_comm.
           rewrite Nat.div_add_l; try lia. simpl. lia.
  - exists 0%nat, 0%Z. auto.
Qed.

Lemma cardinal_eq_refl : forall (T : Type) (A : Ensemble T), ‖ A ‖ = ‖ A ‖.
Proof.
  intros T A. pose proof classic (A = ⦃⦄) as [H1 | H1]; [left | right; repeat split]; auto.
  - exists (fun x => x). split.
    -- intros x y H2. auto.
    -- intros y. exists y. auto.
Qed.

Lemma cardinal_eq_sym : forall (T1 T2 : Type) (A : Ensemble T1) (B : Ensemble T2), ‖ A ‖ = ‖ B ‖ -> ‖ B ‖ = ‖ A ‖.
Proof.
  intros T1 T2 A B [[H1 H2] | [H1 [H2 [f [H3 H4]]]]]; [left | right; repeat split]; auto.
  apply choice in H4 as [g H5]. exists g. split.
  - intros x y H6. specialize (H5 (f (g x))) as H7. rewrite H6 in H7 at 2.
    do 3 rewrite H5 in H7; auto.
  - intros y. specialize (H3 y (g (f y))). specialize (H5 (f y)) as H6.
    rewrite <- H6 in H3 at 1. exists (f y). rewrite H3; auto. rewrite H6. auto.
Qed.

Open Scope nat_scope.

Lemma triangular_number_bounds : forall n,
  exists t, t * (t + 1) / 2 <= n < (t + 1) * (t + 2) / 2.
Proof.
  intros n.
  assert (n = 0 \/ n = 1 \/ n = 2 \/ n > 2) as [H1 | [H1 | [H1 | H1]]] by lia;
    [exists 0 | exists 1 | exists 1 |]; try (simpl; lia).
  set (E t := t * (t + 1) / 2 > n). assert (exists t, E t) as H2.
  { exists n. unfold E. pose proof sum_n_divisible n as [j H3]. rewrite H3. rewrite Nat.div_mul; nia. }
  pose proof WI_SI_WO as [_ [_ WO]]. apply not_Empty_In in H2. apply WO in H2 as [t [H2 H3]].
  exists (t - 1). assert (t = 0 \/ t > 0) as [H4 | H4] by lia.
  - unfold Ensembles.In in H2. rewrite H4 in H2. unfold E in H2. simpl in H2. lia.
  - split.
    -- unfold E in H2. pose proof classic ((t - 1) * (t - 1 + 1) / 2 <= n) as [H5 | H5]; auto.
       apply not_le in H5. specialize (H3 (t - 1) H5); lia.
    -- replace (t - 1 + 1) with t by lia. replace (t - 1 + 2) with (t + 1) by lia. unfold E in H2. auto.
Qed.

Lemma theorem_30_3 : ‖ ℕ ‖ = ‖ ℕ × ℕ ‖.
Proof.
  apply cardinal_eq_sym. unfold cardinal_eq. right. repeat split.
  - apply not_Empty_In. unfold Ensembles.In, set_prod. exists (1, 1), 1, 1. repeat split.
  - apply not_Empty_In. exists 1. apply Full_intro.
  - replace (ℕ × ℕ) with (Full_set (ℕ * ℕ)). 
    2 : { apply set_equal_def. intros [n1 n2]. split; intros H1; try apply Full_intro. exists n1, n2. repeat split. }
    set (f := fun p : ℕ * ℕ => let (n1, n2) := p in (n1 + n2) * (n1 + n2 + 1) / 2 + n2).
    apply exists_bijection with (f := f). split.
    -- intros [m n] [p q] H1. unfold f in H1. assert (m + n < p + q \/ m + n = p + q \/ m + n > p + q) as [H2 | [H2 | H2]] by lia.
       * set (a := m + n). set (d := p + q - a). replace (m + n) with a in H1 by lia. replace (p + q) with (a + d) in H1 by lia.
         assert (H3 : n - q = (a + d) * (a + d + 1) / 2 - a * (a + 1) / 2) by lia.
         replace ((a + d) * (a + d + 1) / 2 - a * (a + 1) / 2) with (a * d + d * (d + 1) / 2) in H3.
         2 :
         { pose proof sum_n_divisible a as [j H4]. pose proof sum_n_divisible (a + d) as [k H5]. pose proof sum_n_divisible d as [i H6].
             rewrite H4, H5, H6. repeat rewrite Nat.div_mul; lia. }
         assert (d = 0 \/ d > 0) as [H4 | H4] by lia; try lia.
         assert (d * (d + 1) / 2 >= 1) as H5. { pose proof sum_n_divisible d as [j H5]. rewrite H5. rewrite Nat.div_mul; lia. }
         assert (a * d + d * (d + 1) / 2 >= a + 1) as H6 by nia. assert (n > a + q) as H7 by lia. unfold a in H7. lia.
       * rewrite H2 in H1. f_equal; lia.
       * set (a := p + q). set (d := m + n - a). replace (p + q) with a in H1 by lia. replace (m + n) with (a + d) in H1 by lia.
         assert (H3 : q - n = (a + d) * (a + d + 1) / 2 - a * (a + 1) / 2) by lia.
         replace ((a + d) * (a + d + 1) / 2 - a * (a + 1) / 2) with (a * d + d * (d + 1) / 2) in H3.
         2 :
         { pose proof sum_n_divisible a as [j H4]. pose proof sum_n_divisible (a + d) as [k H5]. pose proof sum_n_divisible d as [i H6].
             rewrite H4, H5, H6. repeat rewrite Nat.div_mul; try lia. }
         assert (d = 0 \/ d > 0) as [H4 | H4] by lia; try lia.
         assert (d * (d + 1) / 2 >= 1) as H5. { pose proof sum_n_divisible d as [j H5]. rewrite H5. rewrite Nat.div_mul; lia. }
         assert (a * d + d * (d + 1) / 2 >= a + 1) as H6 by nia. assert (n > a + m) as H7 by lia. unfold a in H7. lia.
    -- intros n. pose proof triangular_number_bounds n as [t [H1 H2]]. set (b := n - t * (t + 1) / 2). set (a := t - b). exists (a, b). unfold f.
       unfold a, b. assert (n >= t \/ n < t) as [H3 | H3]; assert (t * (t + 1) / 2 = n \/ t * (t + 1) / 2 < n) as [H4 | H4]; try lia.
       * rewrite H4. replace (n - n) with 0 by lia. rewrite Nat.sub_0_r. repeat rewrite Nat.add_0_r. lia.
       * assert (t >= (n - t * (t + 1) / 2) \/ t < (n - t * (t + 1) / 2)) as [H5 | H5] by lia.
         ** replace ((t - (n - t * (t + 1) / 2) + (n - t * (t + 1) / 2))) with t by nia. lia.
         ** replace (t + 2) with (t + 1 + 1) in H2 by lia. pose proof sum_n_divisible (t+1) as [j H6].
            pose proof (sum_n_divisible t) as [k H7]. rewrite H6 in H2. rewrite H7 in H5. rewrite Nat.div_mul in H2; try lia.
            rewrite Nat.div_mul in H5; lia.
       * rewrite H4. replace (n - n) with 0 by lia. rewrite Nat.sub_0_r. repeat rewrite Nat.add_0_r. auto.
       * replace ((t - (n - t * (t + 1) / 2) + (n - t * (t + 1) / 2))) with t by nia. lia.
Qed.