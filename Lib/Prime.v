From Lib Require Import Imports WI_SI_WO Pigeonhole Reals_util.

Open Scope Z_scope.

Module Znt := ZArith.Znumtheory.
Notation In := List.In.

Definition composite (n : Z) : Prop := (1 < n)%Z /\ ~ Znt.prime n.

Definition prime_list (l : list Z) : Prop := Forall Znt.prime l.

Lemma prime_list_fold_right_pos : forall l,
  prime_list l -> fold_right Z.mul 1 l >= 0.
Proof.
  intros l H1. induction l as [| h t IH].
  - simpl. lia.
  - simpl. apply Forall_cons_iff in H1 as [H1 H2]. apply IH in H2. assert (h >= 2) as H3.
    { apply Znt.prime_ge_2 in H1. lia. }
    lia.
Qed.

Lemma prime_list_app : forall l1 l2,
  prime_list (l1 ++ l2) <-> prime_list l1 /\ prime_list l2.
Proof.
  intros l1 l2. split.
  - intros H1. unfold prime_list in H1. rewrite Forall_app in H1. tauto.
  - intros [H1 H2]. unfold prime_list. rewrite Forall_app. tauto.
Qed.

Lemma in_prime_list : forall l x,
  prime_list l -> In x l -> Znt.prime x.
Proof.
  intros l x H1 H2. unfold prime_list in H1. rewrite Forall_forall in H1. apply H1. auto.
Qed.

Fixpoint max_list_Z (l : list Z) : Z :=
  match (l) with
  | [] => 0
  | x :: xs => Z.max x (max_list_Z xs)
  end.

Lemma in_list_le_max : forall l x,
  In x l -> x <= (max_list_Z l)%Z.
Proof.
  intros l x H. induction l as [| h t IH].
  - inversion H.
  - destruct H as [H | H].
    -- rewrite H. simpl. apply Z.le_max_l.
    -- apply IH in H. simpl. lia.
Qed.

Definition first_n_primes (l : list Z) : Prop :=
  NoDup l /\ prime_list l /\
    (forall x, (Znt.prime x /\ x <= (max_list_Z l)%Z) -> In x l).

Theorem theorem_19_3 : forall a,
  composite a -> exists b c, 1 < b < a /\ 1 < c < a /\ a = b * c.
Proof.
  intros a [H1 H2]. apply Znt.not_prime_divide in H2 as [b [H3 [c H4]]]; auto.
  exists b, c. repeat split; nia.
Qed.

Theorem theorem_19_4 : forall p a,
  Znt.prime p -> ((p | a) -> Z.gcd p a = p) /\ (~(p | a) -> Z.gcd p a = 1).
Proof.
  intros p a H1. split; intros H2.
  - destruct H1 as [H1 _]. apply Z.divide_gcd_iff in H2; lia.
  - destruct (classic (a | p)) as [H3 | H3].
    -- pose proof (Znt.prime_divisors p H1 a H3) as [H4 | [H4 | [H4 | H4]]]; subst.
       * replace (-1) with (-(1)) by lia. rewrite Z.gcd_opp_r. apply Z.gcd_1_r.
       * apply Z.gcd_1_r.
       * exfalso. apply H2; auto.
       * exfalso. apply H2. apply Znt.Zdivide_opp_r. apply Z.divide_refl.
    -- destruct (classic (Z.gcd p a = 1)) as [H4 | H4]; auto. pose proof Z.gcd_nonneg p a as H5. 
       assert (Z.gcd p a = 0 \/ Z.gcd p a > 1) as [H6 | H6]; try lia.
       * apply Z.gcd_eq_0 in H6 as [H6 H7]; subst. exfalso. apply H2. exists 0; lia.
       * pose proof Z.gcd_divide_r p a as H7. apply Znt.prime_alt in H1. destruct H1 as [H0 H1].
         pose proof classic (Z.gcd p a = p) as [H8 | H8].
         + rewrite H8 in H7. tauto.
         + pose proof Z.gcd_divide_l p a as H9. apply Z.divide_pos_le in H9 as H10; try lia. specialize (H1 (Z.gcd p a) ltac:(lia)). tauto.
Qed.

Theorem theorem_19_5 : forall a,
  a > 1 -> Znt.prime a <-> (forall b c, (a | b * c) -> (a | b) \/ (a | c)).
Proof.
  intros a H1. split; intros H2.
  - intros b c H3. rewrite Z.mul_comm in H3. pose proof classic (a | b) as [H4 | H4];
    pose proof classic (a | c) as [H5 | H5]; auto. left.
    apply Z.gauss with (m := c); auto. apply theorem_19_4; auto.
  - pose proof classic (Znt.prime a) as [H3 | H3]; auto.
    pose proof Znt.not_prime_divide a ltac:(lia) H3 as [b [H4 [c H5]]].
    specialize (H2 b c ltac:(exists 1; lia)). destruct H2 as [H2 | H2];
    apply Z.divide_pos_le in H2; nia.
Qed.

Theorem theorem_19_6 : forall p l,
  Znt.prime p -> (p | fold_right Z.mul 1 l) -> exists x, In x l /\ (p | x).
Proof.
  intros p l H1 H2. assert (p > 1) as H3 by (destruct H1; lia). induction l as [| h t IH]; simpl in *.
  - destruct H2 as [x H2]. pose proof Znt.Zmult_one p x ltac:(lia) ltac:(lia); lia.
  - apply theorem_19_5 in H2 as [H4 | H4]; auto.
    -- exists h. split; auto.
    -- specialize (IH H4) as [x [H5 H6]]. exists x. split; auto.
Qed.

Theorem theorem_19_7 : forall a,
  a > 1 -> (exists p, Znt.prime p /\ (p | a)).
Proof.
  intros a. strong_induction a.
  assert (a = 2 \/ a > 2) as [H2 | H2] by lia.
  - exists 2. split; [apply Znt.prime_2 | exists 1; lia].
  - destruct (Znt.prime_dec a) as [H4 | H4].
    -- exists a. split; [auto | exists 1; lia].
    -- rewrite <- Znt.prime_alt in H4. apply not_and_or in H4 as [H4 | H4]; try lia.
       apply not_all_ex_not in H4 as [p H4]. apply imply_to_and in H4 as [H4 H5]. apply NNPP in H5.
       specialize (IH p ltac:(lia) ltac:(lia)). destruct IH as [p' IH]. exists p'. split; try apply IH.
       apply Z.divide_trans with (m := p); tauto.
Qed.

Lemma fold_right_mul_distributive : forall (k : Z) (l : list Z),
  fold_right Z.mul k l = k * fold_right Z.mul 1 l.
Proof.
  intros k l. induction l as [| h l' IH].
  - simpl. lia.
  - simpl. rewrite IH. lia.
Qed.

Theorem theorem_19_8 : forall a : Z,
  a > 1 -> exists l : list Z,
    prime_list l /\ a = fold_right Z.mul 1 l.
Proof.
    intros a. strong_induction a.
    - assert (a = 2 \/ a > 2) as [H2 | H2] by lia.
      -- exists [2]. split; try (simpl; lia); try (constructor; auto). apply Znt.prime_2.
      -- destruct (Znt.prime_dec a) as [H3 | H3].
         + exists [a]. split; try (simpl; lia); try constructor; auto.
         + rewrite <- Znt.prime_alt in H3. apply not_and_or in H3 as [H3 | H3]; try lia.
           apply not_all_ex_not in H3 as [p H3]. apply imply_to_and in H3 as [H4 H5].
           apply NNPP in H5 as [k H5].
           assert (exists l1 : list Z, prime_list l1 /\ p = fold_right Z.mul 1 l1) as [l1 H11] by (apply IH; lia).
           assert (exists l2 : list Z, prime_list l2 /\ k = fold_right Z.mul 1 l2) as [l2 H12] by (apply IH; nia).
           exists (l1 ++ l2). split; try (apply Forall_app; split; tauto).
           rewrite fold_right_app. rewrite fold_right_mul_distributive. lia.
Qed.

Lemma prime_list_cons : forall l p,
  prime_list (p :: l) -> prime_list l /\ Znt.prime p.
Proof.
  intros l p H1. split.
  - apply Forall_inv_tail in H1. apply H1.
  - apply Forall_inv in H1. apply H1.
Qed.

Lemma prime_list_cons_iff : forall l p,
  prime_list (p :: l) <-> prime_list l /\ Znt.prime p.
Proof.
  intros l p. split.
  - apply prime_list_cons.
  - intros [H1 H2]. apply Forall_cons; auto.
Qed.

Lemma p_div_fold_right_In : forall l p,
  prime_list l -> Znt.prime p -> (p | fold_right Z.mul 1 l) -> In p l.
Proof.
  intros l p H1 H2 H3. induction l as [| h t IH].
  - simpl in H3. apply Znt.prime_ge_2 in H2. destruct H3 as [r1 H3]. assert (r1 = 1) as H4 by lia. lia.
  - simpl in H3. apply prime_list_cons in H1 as [H1 H1']. destruct (Z.eq_dec h p) as [H6 | H6].
    -- rewrite H6. left. reflexivity.
    -- right. apply IH; auto. assert (H7 : ~(p | h)).
       { intros H7. apply Znt.prime_div_prime in H7; auto. } apply theorem_19_5 in H3; try tauto.
       destruct H2 as [H2 _]. lia.
Qed.

Lemma p_notin_ndiv_fold_right : forall l p,
  prime_list l -> Znt.prime p -> ~In p l -> ~(p | fold_right Z.mul 1 l).
Proof.
  intros l p H1 H2 H3 H4. apply p_div_fold_right_In in H4; auto.
Qed.

Lemma divide_factor_l : forall a b c,
  (b | c) -> (a * b | a * c).
Proof.
  intros a b c [k H]. exists k. lia.
Qed.

Lemma count_mul_div_fold_right : forall l z,
  In z l -> (z ^ (Z.of_nat (count_occ Z.eq_dec l z)) | fold_right Z.mul 1 l).
Proof.
  intros l z H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct H1 as [H1 | H1].
    -- rewrite H1. destruct (Z.eq_dec z z) as [H2 | H2]; try contradiction. clear H2.
       assert (In z t \/ ~ In z t) as [H2 | H2] by apply classic.
       + replace (Z.of_nat (S (count_occ Z.eq_dec t z))) with (Z.succ (Z.of_nat (count_occ Z.eq_dec t z))) by lia.
         rewrite Z.pow_succ_r. 2 : { lia. } apply divide_factor_l. apply IH; auto.
       + apply (count_occ_not_In Z.eq_dec) in H2. rewrite H2. simpl. exists (fold_right Z.mul 1 t). lia. 
    -- pose proof (Z.eq_dec h z) as [H2 | H2].
       + rewrite H2. destruct (Z.eq_dec z z) as [H3 | H3]; try contradiction. clear H3.
         replace (Z.of_nat (S (count_occ Z.eq_dec t z))) with (Z.succ (Z.of_nat (count_occ Z.eq_dec t z))) by lia.
         rewrite Z.pow_succ_r. 2 : { lia. } apply divide_factor_l. apply IH; auto.
       + destruct (Z.eq_dec h z) as [H3 | H3]; try contradiction. apply IH in H1. destruct H1 as [r H1]. exists (r * h). lia.
Qed.

Lemma z_pow_div_z_div : forall a b c,
  c >= 1 -> (a^c | b) -> (a | b).
Proof.
  intros a b c H1 [k H2]. exists (k * a^(Z.pred c)). rewrite H2.
  - assert (c = 1 \/ c > 1) as [H3 | H3] by lia.
    + rewrite H3. simpl. lia.
    + assert (H4 : exists d, c = Z.succ d) by (exists (Z.pred c); lia). destruct H4 as [d H4]. rewrite H4. rewrite Z.pow_succ_r. 2 : { lia. }
      replace (Z.pred (Z.succ d)) with d by lia. lia.
Qed.

Lemma z_pow_mult : forall a b c,
  a >= 0 -> b >= 0 -> c >= 0 -> a^(b) * a^(c) = a^(b + c).
Proof.
  intros a b c H1 H2 H3. rewrite Z.pow_add_r; lia.
Qed.

Lemma z_mul_div : forall a b c,
  c <> 0 ->
  (c | b) -> a * (b / c) = (a * b) / c.
Proof.
  intros a b c H1 [r1 H2]. rewrite H2. rewrite Z.div_mul; auto. 
  rewrite Z.mul_assoc. rewrite Z.div_mul; auto.
Qed.

Lemma fold_right_div_pow_eq_remove_fold_right : forall l z,
  z <> 0 ->
  fold_right Z.mul 1 l / (z ^ (Z.of_nat (count_occ Z.eq_dec l z))) = fold_right Z.mul 1 (remove Z.eq_dec z l).
Proof.
  intros l z H1. induction l as [| h t IH].
  - simpl. apply Z.div_1_r.
  - assert (In z (h :: t) \/ ~ In z (h :: t)) as [H2 | H2] by apply classic.
    -- simpl. destruct (Z.eq_dec h z) as [H3 | H3].
       + rewrite H3. destruct (Z.eq_dec z z) as [H4 | H4]; try contradiction. clear H4.
         assert (In z t \/ ~ In z t) as [H4 | H4] by apply classic.
         * rewrite <- IH. rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r. 2 : { lia. } pose proof (count_mul_div_fold_right t z H4) as [r H5].
           rewrite H5. rewrite Z.div_mul. 2 : { apply (count_occ_In Z.eq_dec) in H4. apply Z.pow_nonzero. lia. lia. } rewrite Z.mul_comm. rewrite <- Z.mul_assoc.
              replace (z^Z.of_nat (count_occ Z.eq_dec t z) * z) with (z * z^Z.of_nat (count_occ Z.eq_dec t z)) by lia. rewrite Z.div_mul; try lia.
              assert (H6 : z ^ Z.of_nat (count_occ Z.eq_dec t z) <> 0). { apply Z.pow_nonzero; lia. } lia.
         * replace (count_occ Z.eq_dec t z) with (0%nat). 2 : { apply (count_occ_not_In Z.eq_dec) in H4. lia. }
           replace (remove Z.eq_dec z t) with t. 2 : { apply (notin_remove Z.eq_dec) in H4. auto. } rewrite Z.mul_comm. replace (Z.of_nat 1) with 1 by lia.
           rewrite Z.pow_1_r. rewrite Z.div_mul; try lia.
       + destruct (Z.eq_dec z h) as [H4 | H4]; try lia. clear H4. simpl. rewrite <- IH. destruct H2 as [H2 | H2]; try contradiction. pose proof (count_mul_div_fold_right t z H2) as [r H4].
         rewrite H4. rewrite Z.div_mul. 2 : { apply (count_occ_In Z.eq_dec) in H2. apply Z.pow_nonzero. lia. lia. } rewrite Z.mul_comm. rewrite <- Z.mul_assoc.
         replace (z^Z.of_nat (count_occ Z.eq_dec t z) * h) with (h * z^Z.of_nat (count_occ Z.eq_dec t z)) by lia. rewrite Z.mul_assoc. rewrite Z.div_mul; try lia.
         apply (count_occ_In Z.eq_dec) in H2. apply Z.pow_nonzero; lia.
    -- replace (remove Z.eq_dec z (h :: t)) with (h :: t). 2 : { apply (notin_remove Z.eq_dec) in H2. auto. } 
       replace (count_occ Z.eq_dec (h :: t) z) with (0%nat). 2 : { apply (count_occ_not_In Z.eq_dec) in H2. lia. } simpl. rewrite Z.div_1_r. lia.
Qed.

Lemma p_ndiv_fold_right : forall l p,
  prime_list l -> In p l -> ~(p | (fold_right Z.mul 1 l / p ^ (Z.of_nat (count_occ Z.eq_dec l p)))).
Proof.
  intros l p H1 H2. rewrite fold_right_div_pow_eq_remove_fold_right. 
  2 : { apply in_prime_list in H2; auto. apply Znt.prime_ge_2 in H2; lia. }
  intros H3. assert (~In p (remove Z.eq_dec p l)) as H4. { intros H4. apply (in_remove Z.eq_dec) in H4. lia. }
  apply H4. apply p_div_fold_right_In; auto. 2 : { apply in_prime_list in H2; auto. } unfold prime_list in *.
  rewrite Forall_forall in *. intros x H5. apply H1. apply in_remove in H5. tauto.
Qed.

Lemma FTA_unique : forall l1 l2 z p,
  prime_list l1 -> prime_list l2 -> z = fold_right Z.mul 1 l1 -> z = fold_right Z.mul 1 l2 -> 
  count_occ Z.eq_dec l1 p = count_occ Z.eq_dec l2 p.
Proof.
  intros l1 l2 z p H1 H2 H3 H4.
  pose proof (lt_eq_lt_dec (count_occ Z.eq_dec l1 p) (count_occ Z.eq_dec l2 p)) as [[H5 | H5] | H5]; auto.
  - assert (H6 : In p l2). { apply (count_occ_In Z.eq_dec); lia. } pose proof (count_mul_div_fold_right l2 p H6) as H7.
    rewrite <- H4 in H7. assert (count_occ Z.eq_dec l1 p = 0 \/ count_occ Z.eq_dec l1 p > 0)%nat as [H8 | H8] by lia.
    -- assert (H9 : ~In p l1). { intros H9. apply (count_occ_not_In Z.eq_dec) in H9. lia. lia. } 
       assert (H10 : ~(p | fold_right Z.mul 1 l1)). { apply p_notin_ndiv_fold_right; auto. apply in_prime_list in H6; auto. }
       rewrite <- H3 in H10. assert (H11 : (p | z)). { apply z_pow_div_z_div with (c := Z.of_nat (count_occ Z.eq_dec l2 p)); auto; lia. } tauto.
    -- assert (H9 : In p l1). { apply (count_occ_In Z.eq_dec); lia. } pose proof (count_mul_div_fold_right l1 p H9) as H10.
       rewrite <- H3 in H10. assert (H11 : (p | z / p ^ (Z.of_nat (count_occ Z.eq_dec l1 p)))).
       { destruct H7 as [r1 H7]. destruct H10 as [r2 H10]. exists (r1 * p ^ Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p - 1)). rewrite H10. rewrite Z.div_mul. 
         2 : { apply Z.pow_nonzero; try lia. apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6; lia. }
         rewrite <- Z.mul_assoc. rewrite Z.mul_comm with (m := p). rewrite <- Z.pow_succ_r; try lia.
         replace (Z.succ (Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p - 1))) with (Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p)) by lia.
         rewrite Nat2Z.inj_sub; try lia. rewrite Z.pow_sub_r; try lia. 2 : { apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6; lia. }
         assert (H12 : (p ^ Z.of_nat (count_occ Z.eq_dec l1 p) | p ^ Z.of_nat (count_occ Z.eq_dec l2 p))). 
         { exists (p ^ (Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p))). rewrite z_pow_mult; try lia. 
           2 : { apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6; lia. }
           replace (Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p) + Z.of_nat (count_occ Z.eq_dec l1 p)) with (Z.of_nat (count_occ Z.eq_dec l2 p)) by lia. lia. 
         }
         rewrite z_mul_div; auto. 2 : { apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6; lia. }
         rewrite <- H7. rewrite H10. rewrite Z.div_mul; auto. apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6; lia.
       }
       pose proof p_ndiv_fold_right l1 p H1 H9 as H12. rewrite <- H3 in H12. tauto.
  - assert (H6 : In p l1). { apply (count_occ_In Z.eq_dec); lia. } pose proof (count_mul_div_fold_right l1 p H6) as H7.
    rewrite <- H3 in H7. assert (count_occ Z.eq_dec l2 p = 0 \/ count_occ Z.eq_dec l2 p > 0)%nat as [H8 | H8] by lia.
    -- assert (H9 : ~In p l2). { intros H9. apply (count_occ_not_In Z.eq_dec) in H9. lia. lia. } 
       assert (H10 : ~(p | fold_right Z.mul 1 l2)). { apply p_notin_ndiv_fold_right; auto. apply in_prime_list in H6; auto. }
       rewrite <- H4 in H10. assert (H11 : (p | z)). { apply z_pow_div_z_div with (c := Z.of_nat (count_occ Z.eq_dec l1 p)); auto; lia. }
       tauto.
    -- assert (H9 : In p l2). { apply (count_occ_In Z.eq_dec); lia. } pose proof (count_mul_div_fold_right l2 p H9) as H10.
       rewrite <- H4 in H10. assert (H11 : (p | z / p ^ (Z.of_nat (count_occ Z.eq_dec l2 p)))).
       { destruct H7 as [r1 H7]. destruct H10 as [r2 H10]. exists (r1 * p ^ Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p - 1)). rewrite H10. rewrite Z.div_mul.
         2 : { apply Z.pow_nonzero; try lia. apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6; lia. }
         rewrite <- Z.mul_assoc. rewrite Z.mul_comm with (m := p). rewrite <- Z.pow_succ_r; try lia.
         replace (Z.succ (Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p - 1))) with (Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p)) by lia.
         rewrite Nat2Z.inj_sub; try lia. rewrite Z.pow_sub_r; try lia. 2 : { apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6; lia. }
         assert (H12 : (p ^ Z.of_nat (count_occ Z.eq_dec l2 p) | p ^ Z.of_nat (count_occ Z.eq_dec l1 p))). 
         { exists (p ^ (Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p))). rewrite z_pow_mult; try lia. 
           2 : { apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6; lia. }
           replace (Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p) + Z.of_nat (count_occ Z.eq_dec l2 p)) with (Z.of_nat (count_occ Z.eq_dec l1 p)) by lia. lia. 
         }
         rewrite z_mul_div; auto. 2 : { apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6; lia. }
         rewrite <- H7. rewrite H10. rewrite Z.div_mul; auto. apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6; lia.
       }
       pose proof p_ndiv_fold_right l2 p H2 H9 as H12. rewrite <- H4 in H12. tauto.
Qed.

Module ZOrder.
Definition t := Z.
Definition leb := Z.leb.
Lemma leb_total : forall x y : t, leb x y = true \/ leb y x = true.
Proof.
  intros x y; case (Zle_bool_total x y); auto.
Qed.
End ZOrder.

Module ZSort := Sort ZOrder.

Lemma Transitive_Zle_bool : Transitive (fun x y => is_true (x <=? y)%Z).
Proof.
  intros a; unfold is_true; lia.
Qed.

Lemma Sorted_bool_prop : forall l : list Z,
  Sorted Z.le l <-> Sorted ((fun x y => is_true (x <=? y)%Z)) l.
Proof.
  intros l. split.
  - induction l as [| x xs IH].
    -- constructor.
    -- inversion 1; subst. constructor.
      + apply IH. assumption.
      + inversion H3. constructor. unfold is_true. constructor. lia.
  - induction l as [| x xs IH].
    -- constructor. 
    -- inversion 1; subst. constructor.
       + apply IH. assumption.
       + unfold is_true in H3. inversion H3. constructor. constructor. lia.
Qed.

Lemma exists_sorted:  forall (l1 : list Z), exists l2 : list Z, 
  Sorted Z.le l2 /\ Permutation l1 l2.
Proof.
  intros l. exists (ZSort.sort l). rewrite Sorted_bool_prop.
  split;[apply ZSort.Sorted_sort; apply Transitive_Zle_bool | apply ZSort.Permuted_sort].
Qed.

Lemma In_0_fold_right_eq_0_Z : forall l,
  In 0 l -> fold_right Zmult 1 l = 0.
Proof.
  intros l H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct H1 as [H1 | H1].
    + rewrite H1. nia.
    + specialize (IH H1). simpl. nia.
Qed.

Lemma fold_right_factor_divides : forall (k : Z) (l : list Z),
  (In k l) -> (k | fold_right Z.mul 1 l).
Proof.
  intros k l H. induction l as [| h l' IH].
  - inversion H.
  - simpl. destruct H as [H | H].
    -- rewrite H. apply Z.divide_factor_l.
    -- apply IH in H. destruct H as [r H]. exists (r * h). lia.
Qed.

Fixpoint remove_one {A : Type} (eq_dec : forall (x y : A), sumbool (x = y) (x <> y))
                        (a : A) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => if eq_dec x a then xs else x :: remove_one eq_dec a xs
  end.        

Lemma fold_right_Zmult_remove_one_In : forall a l,
  In a l -> (a <> 0) -> fold_right Zmult 1 (remove_one Z.eq_dec a l) = fold_right Zmult 1 l / a.
Proof.
  intros a l H1 H2. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct H1 as [H1 | H1].
    + rewrite H1. destruct (Z.eq_dec a a) as [H3 | H3]; try contradiction. rewrite Z.mul_comm. rewrite Z.div_mul; lia.
    + specialize (IH H1). destruct (Z.eq_dec h a) as [H3 | H3]. rewrite H3. rewrite Z.mul_comm. rewrite Z.div_mul; lia.
      simpl. rewrite IH. pose proof (fold_right_factor_divides a t ltac:(auto)) as [k H4]. rewrite H4. rewrite Z.div_mul; try nia.
      replace (h * (k * a)) with ((h * k) * a) by lia. rewrite Z.div_mul; lia. 
Qed.

Lemma remove_one_In : forall {A : Type} eq_dec (a : A) l,
  List.In a l -> count_occ eq_dec (remove_one eq_dec a l) a = pred (count_occ eq_dec l a).
Proof.
  intros A eq_dec a l H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct (eq_dec h a) as [H2 | H2].
    + simpl. reflexivity.
    + simpl. destruct H1 as [H1 | H1].
      * rewrite H1 in H2. contradiction.
      * rewrite IH; auto. destruct (eq_dec h a) as [H3 | H3]; try contradiction. reflexivity.
Qed.

Lemma remove_one_In_length : forall {A : Type} eq_dec (a : A) l,
  List.In a l -> length (remove_one eq_dec a l) = pred (length l).
Proof.
  intros A eq_dec a l H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct (eq_dec h a) as [H2 | H2].
    + simpl. reflexivity.
    + simpl. destruct H1 as [H1 | H1].
      * rewrite H1 in H2. contradiction.
      * rewrite IH; auto. destruct t.
        -- inversion H1.
        -- simpl. reflexivity.
Qed.

Lemma remove_one_not_In : forall {A : Type} eq_dec (a : A) l,
  ~List.In a l -> remove_one eq_dec a l = l.
Proof.
  intros A eq_dec a l H1. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (eq_dec h a) as [H2 | H2].
    + rewrite H2 in H1. rewrite not_in_cons in H1. tauto.
    + simpl. rewrite IH; auto. rewrite not_in_cons in H1. tauto.
Qed.

Lemma count_occ_remove_one_not_eq : forall {A : Type} eq_dec (a b : A) l,
  a <> b -> count_occ eq_dec (remove_one eq_dec a l) b = count_occ eq_dec l b.
Proof.
  intros A eq_dec a b l H1. induction l as [| h t IH].
  - simpl. reflexivity.
  - simpl. destruct (eq_dec h a) as [H2 | H2].
    + destruct (eq_dec h b) as [H3 | H3].
      * rewrite H3 in H2. rewrite H2 in H1. contradiction.
      * reflexivity.
    + destruct (eq_dec h b) as [H3 | H3].
      * rewrite H3. simpl. destruct (eq_dec b b) as [H4 | H4]; try contradiction. rewrite IH. reflexivity.
      * simpl. destruct (eq_dec h b) as [H4 | H4]; try contradiction. rewrite IH. reflexivity.
Qed.

Lemma In_remove_one : forall {A : Type} eq_dec (a b : A) l,
  List.In a l -> a <> b -> List.In a (remove_one eq_dec b l).
Proof.
  intros A eq_dec a b l H1 H2. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct (eq_dec h b) as [H3 | H3].
    + destruct H1 as [H1 | H1].
      * rewrite H1 in H3. contradiction.
      * auto.
    + destruct H1 as [H1 | H1].
      * rewrite H1. left. reflexivity.
      * right. apply IH; auto.
Qed.

Lemma In_remove_one_In_l : forall {A : Type} eq_dec (a b : A) l,
  List.In a (remove_one eq_dec b l) -> List.In a l.
Proof.
  intros A eq_dec a b l H1. induction l as [| h t IH].
  - simpl in H1. contradiction.
  - simpl in H1. destruct (eq_dec h b) as [H2 | H2].
    + right; auto.
    + destruct H1 as [H1 | H1].
      * left. auto.
      * right. apply IH; auto.
Qed.

Lemma count_occ_eq_len : forall (A : Type) (eq_dec : forall x y : A, {x = y} + {x <> y}) (l1 l2 : list A),
  (forall x, count_occ eq_dec l1 x = count_occ eq_dec l2 x) -> length l1 = length l2.
Proof.
  intros A eq_dec l1 l2. revert l2. induction l1 as [| h1 t1 IH].
  - intros l2 H1. simpl. destruct l2; auto. specialize (H1 a). simpl in H1. destruct (eq_dec a a); auto. lia. contradiction.
  - intros l2 H1. destruct l2 as [| h2 t2].
    + specialize (H1 h1). simpl in H1. destruct (eq_dec h1 h1); auto. lia. contradiction.
    + simpl. f_equal. destruct (eq_dec h1 h2) as [H2 | H2].
      * apply IH. intros x. specialize (H1 x). assert (h1 = x \/ h1 <> x) as [H3 | H3] by apply classic.
        -- subst. rewrite count_occ_cons_eq in H1; rewrite count_occ_cons_eq in H1; auto.
        -- rewrite count_occ_cons_neq in H1; rewrite count_occ_cons_neq in H1; auto. rewrite <- H2. auto.
      * assert (length t2 = 0 \/ length t2 > 0)%nat as [H3 | H3] by lia. 
        -- rewrite length_zero_iff_nil in H3. subst. specialize (H1 h1). simpl in H1. destruct (eq_dec h1 h1); 
            destruct (eq_dec h2 h1); try contradiction; try lia. exfalso. apply H2. auto.
        -- specialize (IH (h2 :: (remove_one eq_dec h1 t2))). replace (length (h2 :: remove_one eq_dec h1 t2))
           with (length t2) in IH. apply IH. intros x. destruct (eq_dec h2 x) as [H4 | H4].
           ++ rewrite count_occ_cons_eq; auto. rewrite count_occ_remove_one_not_eq. specialize (H1 x).
              rewrite <- H4 in H1. rewrite count_occ_cons_neq in H1; auto. rewrite count_occ_cons_eq in H1; auto.
              rewrite <- H4. auto. intros H5. apply H2. rewrite H4, H5. auto.
           ++ destruct (eq_dec h1 x) as [H5 | H5].
              ** rewrite count_occ_cons_neq; auto. specialize (H1 x). rewrite <- H5 in H1. rewrite count_occ_cons_eq in H1; auto.
                 rewrite count_occ_cons_neq in H1; auto. rewrite H5. rewrite remove_one_In. rewrite <- H5. lia.
                 rewrite <- H5. rewrite (count_occ_In eq_dec). lia.
              ** rewrite count_occ_cons_neq; auto. rewrite count_occ_remove_one_not_eq; auto. specialize (H1 x).
                 rewrite count_occ_cons_neq in H1; auto. rewrite count_occ_cons_neq in H1; auto.
           ++ simpl. rewrite remove_one_In_length. lia. specialize (H1 h1). rewrite count_occ_cons_eq in H1; auto.
              rewrite count_occ_cons_neq in H1; auto. rewrite (count_occ_In eq_dec). lia.
Qed.

Lemma count_occ_eq_prod_right : forall l1 l2,
  (forall n, count_occ Z.eq_dec l1 n = count_occ Z.eq_dec l2 n) -> fold_right Zmult 1 l1 = fold_right Zmult 1 l2.
Proof.
  intros l1 l2 H1. generalize dependent l2. induction l1 as [| h t IH].
  - intros l2 H1. simpl in *. assert (H2 : forall n, count_occ Z.eq_dec l2 n = 0%nat) by (intros n; specialize (H1 n); lia). 
    apply count_occ_inv_nil in H2. rewrite H2. reflexivity.
  - intros l2 H1. simpl. specialize (IH (remove_one Z.eq_dec h l2)). rewrite IH.
    2 : { 
      intros z. assert (In z l2 \/ ~In z l2) as [H3 | H3] by apply classic.
      - assert (h = z \/ h <> z) as [H4 | H4] by apply classic.
        -- rewrite H4 in *. specialize (H1 z). rewrite count_occ_cons_eq in H1; auto. rewrite remove_one_In; auto. lia.
        -- specialize (H1 z). rewrite count_occ_cons_neq in H1; auto. rewrite count_occ_remove_one_not_eq; auto.
      - assert (h = z \/ h <> z) as [H4 | H4] by apply classic.
        -- rewrite H4 in *. specialize (H1 z). apply (count_occ_not_In Z.eq_dec) in H3. rewrite H3 in H1. rewrite count_occ_cons_eq in H1; auto. lia.
        -- specialize (H1 z). rewrite count_occ_cons_neq in H1; auto. rewrite count_occ_remove_one_not_eq; auto.
    }
    specialize (H1 h). rewrite count_occ_cons_eq in H1; auto. assert (In h l2) as H3.
    { rewrite (count_occ_In Z.eq_dec). lia. } assert (h = 0 \/ h <> 0) as [H4 | H4] by nia. rewrite H4. rewrite In_0_fold_right_eq_0_Z with (l := l2); try lia. rewrite <- H4. auto.
     rewrite fold_right_Zmult_remove_one_In; auto. pose proof fold_right_factor_divides h l2 ltac:(auto) as [k H5]. rewrite H5. rewrite Z.div_mul; lia.
Qed.

Lemma fold_right_Rmult_Permutation : forall l1 l2,
  Permutation l1 l2 -> fold_right Z.mul 1 l1 = fold_right Z.mul 1 l2.
Proof.
  intros l1 l2 H1. rewrite (Permutation_count_occ Z.eq_dec) in H1. apply count_occ_eq_prod_right; auto.
Qed.

Lemma HdRel_trans : forall l x y,
  HdRel Z.le y l -> x <= y -> HdRel Z.le x l.
Proof.
  intros l x y H1 H2. induction l as [| h t IH].
  - apply HdRel_nil.
  - apply HdRel_cons. apply HdRel_inv in H1. lia.
Qed.

Lemma Sorted_cons_In : forall l x y,
  Sorted Z.le (x :: l) -> In y l -> x <= y.
Proof.
  intros l x y H1 H2. induction l as [| h t IH].
  - inversion H2.
  - apply Sorted_inv in H1 as [H1 H3]. apply HdRel_inv in H3; auto. inversion H2 as [H4 | H4]; try nia. apply IH; auto.
    apply Sorted_cons; repeat apply Sorted_inv in H1 as [H5 H6]; auto. apply HdRel_trans with (y := h); auto.
Qed.

Lemma Sorted_Permutation_equal : forall l1 l2,
  Permutation l1 l2 -> Sorted Z.le l1 -> Sorted Z.le l2 -> l1 = l2.
Proof.
  intros l1 l2 H1 H2 H3. generalize dependent l2. induction l1 as [| h1 t1 IH].
  - intros l2 H1 H3. apply Permutation_nil in H1. rewrite H1. reflexivity.
  - intros l2 H3 H4. destruct l2 as [| h2 t2].
    -- apply Permutation_sym in H3. apply Permutation_nil in H3. auto.
    -- apply Sorted_inv in H2 as [H2 H5]. specialize (IH H2 t2). assert (In h1 (h1 :: t1) -> In h1 (h2 :: t2)) as H6.
       { apply Permutation_in; auto. } assert (In h2 (h2 :: t2) -> In h2 (h1 :: t1)) as H7.
       { apply Permutation_in. apply Permutation_sym; auto. } assert (In h1 (h2 :: t2)) as H8 by (apply H6; left; reflexivity).
       assert (In h2 (h1 :: t1)) as H9 by (apply H7; left; reflexivity). assert (h1 = h2) as H10.
       {
        destruct H8 as [H8 | H8]; destruct H9 as [H9 | H9]; try lia; try inversion H8; try inversion H9. pose proof (Z.lt_trichotomy h1 h2) as [H10 | [H10 | H10]]; try nia.
        - assert (h2 <= h1) as H11. { apply Sorted_cons_In with (x := h2) (l := t2); auto. } lia.
        - assert (h1 <= h2) as H11. { apply Sorted_cons_In with (x := h1) (l := t1); auto. } lia.
       }
       
      rewrite H10. apply f_equal. apply IH.
      rewrite <- H10 in H3. apply Permutation_cons_inv in H3; auto. apply Sorted_inv in H4 as [H4 H11]; auto.
Qed.

Theorem theorem_19_9 : forall n,
  n > 1 -> exists! l, prime_list l /\ Sorted Z.le l /\ n = fold_right Z.mul 1 l.
Proof.
  intros n H1. pose proof theorem_19_8 n H1 as [l [H2 H3]]. pose proof exists_sorted l as [l2 [H4 H5]].
  exists l2; repeat split; auto.
  - unfold prime_list in *. rewrite Forall_forall in *. intros x H6. apply H2. apply Permutation_sym in H5.
    apply (Permutation_in x) in H5; auto.
  - pose proof theorem_19_8 n ltac:(lia) as [l3 [H6 H7]]. apply fold_right_Rmult_Permutation in H5. lia.
  - intros l3 [H6 [H7 H8]]. apply Sorted_Permutation_equal; auto. rewrite (Permutation_count_occ Z.eq_dec). intros x.
    apply FTA_unique with (z := n); auto. 2 : { rewrite H3. apply fold_right_Rmult_Permutation; auto. }
    apply Forall_forall; intros y H9. apply Permutation_sym in H5. apply (Permutation_in y) in H5; auto.
    unfold prime_list in H2. rewrite Forall_forall in H2. apply H2; auto.
Qed.

Lemma prime_list_product_gt_1 : forall l,
  prime_list l -> fold_right Z.mul 1 l >= 1.
Proof.
  intros l H1. induction l as [| h t IH].
  - simpl. lia.
  - simpl. unfold prime_list in *. apply Forall_cons_iff in H1 as [H1 H2]. apply IH in H2.
    assert (h >= 2) as H3. { apply Znt.prime_ge_2 in H1. lia. }
    lia.
Qed.

Lemma prime_no_div : forall p z,
  Znt.prime p -> (p | z) -> ~(p | z + 1).
Proof.
  intros p z H1 H2 H3. destruct H2 as [r H2]. destruct H3 as [s H3].
  assert (p | 1) as H4 by (exists (s - r); lia). assert (p >= 2) as H5.
  { apply Znt.prime_ge_2 in H1. lia. }
  assert (p = 1) as H6. { destruct H4 as [t H4]. assert (t > 0) by lia. nia. }
  lia.
Qed.

Theorem theorem_19_14_a : forall (l : list Z),
  first_n_primes l -> exists p : Z, Znt.prime p /\ p > max_list_Z l.
Proof.
  intros l [H1 [H2 H3]]. set (N := fold_right Z.mul 1 l + 1).
  assert (N > 1) as H4 by (destruct l; apply prime_list_product_gt_1 in H2; lia).
  destruct (theorem_19_7 N H4) as [q [H5 H6]]. exists q. split; auto.
  destruct (in_dec Z.eq_dec q l) as [H7 | H7].
  - assert ((q | fold_right Z.mul 1 l)) as H8 by (apply fold_right_factor_divides; auto).
    unfold N in H6. pose proof (prime_no_div q (fold_right Z.mul 1 l) H5 H8 H6) as H9. lia.
  - specialize (H3 q). tauto. 
Qed.

Lemma gt_list_max_not_in : forall l x,
  (x > max_list_Z l)%Z -> ~(In x l).
Proof.
  intros l x H1 H2. induction l as [| h t IH].
  - inversion H2.
  - simpl in H1. simpl in H2. destruct H2 as [H2 | H2].
    -- rewrite H2 in H1. lia.
    -- apply IH in H2. lia. lia.
Qed.

Lemma le_max_list_Z : forall l x z,
  x <= max_list_Z (z :: l) -> x = z \/ (x < z /\ x > max_list_Z l) \/ x <= max_list_Z l.
Proof.
  intros l x z H1. induction l as [| h l' IH].
  - simpl in *. assert (H2 : z <= 0 \/ z > 0) by lia. destruct H2.
    -- lia.
    -- lia.
  - simpl in *. assert (H2 : z <= h \/ z > h) by lia. destruct H2.
    -- simpl in H1. lia.
    -- simpl in H1. lia.
Qed.

Lemma prime_list_len : forall n,
  exists l, first_n_primes l /\ length l = n.
Proof.
  intros n. induction n as [| k IH].
  - exists []. split.
    -- repeat split; repeat constructor. intros x [H1 H2]. simpl in H2.
       assert (H3 : x >= 2) by (apply Znt.prime_ge_2 in H1; lia). lia.
    -- simpl. reflexivity.
  - destruct IH as [l [H1 H2]]. destruct (theorem_19_14_a l H1) as [p [H3 H4]].
    set (E := (fun x => (Znt.prime x /\ x > max_list_Z l)%Z)).
    assert (exists p, E p) as [p' H5]. { exists p. unfold E. split; auto. }
    assert (H6 : forall z, E z -> z >= 0).
    { intros z [H6 H7]. assert (z >= 2). { apply Znt.prime_ge_2 in H6. lia. } lia. }
    assert (H7 : exists z, E z). { exists p'. apply H5. }
    pose proof (well_ordering_Z E H6 H7) as [z [[H8 H9] H10]].
    exists (z :: l). split.
    -- repeat split.
      + constructor. apply gt_list_max_not_in. lia. unfold first_n_primes in H1. tauto.
      + unfold prime_list. unfold first_n_primes in H1; apply Forall_cons; tauto.
      + intros x [H11 H12]. simpl. apply le_max_list_Z in H12 as [H12 | [H12 | H12]].
        * lia.
        * destruct H12 as [H12 H13]. specialize (H10 x). assert (x >= 0) as H14.
          { apply Znt.prime_ge_2 in H11. lia. }
          assert (E x) as H15. { unfold E. split. apply H11. apply H13. }
          apply H10 in H15. 2 : { apply H14. } lia.
        * right. apply H1. split. apply H11. apply H12.
    -- simpl. lia.
Qed.

Lemma list_len_cons : forall h (l : list Z),
  length (h :: l) = S (length l).
Proof.
  intros h l. simpl. reflexivity.
Qed.

Lemma max_list_cons_ge : forall l h m,
  m >= max_list_Z (h :: l) -> m >= h /\ m >= max_list_Z l.
Proof.
  intros l h m H. induction l as [| h' l' IH].
  - simpl in *. lia.
  - simpl in *. assert (m >= h /\ m >= max_list_Z l') as [H1 H2] by lia. split.
    -- lia.
    -- lia.
Qed.

Lemma max_list_ge_not_in : forall l h,
  h > 0 -> h >= max_list_Z l /\ ~ In h l -> h > max_list_Z l.
Proof.
  intros l h H1 [H2 H3]. induction l as [| h' l' IH].
  - simpl. lia.
  - simpl. assert (~ In h l') as H4. { pose proof in_cons h' h l' as H4. tauto. }
    assert (h >= max_list_Z l') as H5. { apply max_list_cons_ge in H2 as [H2 H6]. apply IH in H4 as H7. lia. lia. }
    assert (H6 : h > max_list_Z l'). { apply IH in H4 as H6. lia. lia. }
    assert (H7 : h <> h'). { intros H7. rewrite H7 in H3. assert (In h' (h' :: l')) as H8 by apply in_eq. tauto. }
    pose proof (max_list_cons_ge l' h' h) as [H8 H9]. lia. lia.
Qed.

Lemma max_list_ge_not_in' : forall l h,
  max_list_Z l > 0 -> max_list_Z l >= h /\ ~ In h l -> max_list_Z l > h.
Proof.
  intros l h H1 [H2 H3]. induction l as [| h' l' IH].
  - simpl in *. lia.
  - simpl. assert (~ In h l') as H4. { pose proof in_cons h' h l' as H4. tauto. }
    assert (max_list_Z (h' :: l') = h' \/ max_list_Z (h' :: l') = max_list_Z l') as [H5 | H5] by (simpl; lia).
    -- rewrite H5 in H2. assert (h' <> h) as H6.
       { intros H6. rewrite H6 in H3. assert (In h' (h' :: l')) as H7 by apply in_eq. rewrite H6 in H7. tauto. } lia.
    -- assert (max_list_Z l' >= h) as H6. { rewrite H5 in H2. tauto. }
       assert (max_list_Z l' > h) as H7. { apply IH in H4 as H7; lia; auto. }
       lia.
Qed.

Definition Zseq_pos (seq : list nat) : list Z :=
  map Z.of_nat (seq).

Lemma in_Zseq_pos : forall start len x,
  let l := seq start len in
    x > 0 -> In (Z.to_nat x) (seq start len) -> In x (Zseq_pos l).
Proof.
  intros start len x l H. unfold Zseq_pos.
  rewrite in_map_iff. exists (Z.to_nat x). split. lia. auto.
Qed.

Lemma Zseq_len : forall start len,
  let l := seq start len in
    length (l) = length (Zseq_pos l).
Proof.
  intros start len. unfold Zseq_pos. rewrite length_map. reflexivity.
Qed.

Lemma in_list_1 : forall l,
  Z.of_nat (length l) > 0 -> NoDup l -> Forall (fun x => x > 0) l -> Z.of_nat (length l) = max_list_Z l -> In 1 l.
Proof.
  intros l H1 H2 H3 H4. destruct (in_dec Z.eq_dec 1 l) as [H5 | H5]. apply H5.
  set (l2 := Zseq_pos (seq 2 (Z.to_nat (max_list_Z l - 1)))). assert (~NoDup l) as H6.
  - apply pigeonhole_principle_list with (l2 := l2).
    2 : { assert (length l2 = Z.to_nat (max_list_Z l) - 1)%nat. { unfold l2. rewrite <- Zseq_len. rewrite length_seq. lia. } lia. }
    intros x H6. apply in_Zseq_pos. rewrite Forall_forall in H3. specialize (H3 x). tauto. apply in_seq.
    replace (2 + Z.to_nat (max_list_Z l - 1))%nat with (Z.to_nat (max_list_Z l) + 1)%nat by lia. pose proof H6 as H6'. pose proof H6 as H6''.
    apply in_list_le_max in H6. rewrite Forall_forall in H3. specialize (H3 x). apply H3 in H6'. assert (~x = 1). unfold not in *. intros H7. apply H5. rewrite H7 in H6''. tauto.
    lia.
  - tauto.
Qed.

Lemma list_len_lt_max : forall l,
  Forall (fun x => x > 1) l /\ NoDup l -> Z.of_nat (length l) <= max_list_Z l.
Proof.
  intros l. induction l as [| h l' IH].
  - intros [H1 H2]. simpl. lia.
  - intros [H1 H2]. apply Forall_cons_iff in H1 as [H1 H1']. apply NoDup_cons_iff in H2 as [H2 H3].
    assert (Z.of_nat(length l') <= max_list_Z l') as H4 by (apply IH; split; auto).
    rewrite list_len_cons. assert (max_list_Z (h :: l') = h \/ max_list_Z (h :: l') = max_list_Z l') as [H5 | H5] by (simpl; lia).
    -- rewrite H5. assert (H6 : h >= max_list_Z l') by (induction l'; simpl in *; lia).
       pose proof (max_list_ge_not_in l' h) as H7. assert (H8 : h > 0) by lia. apply H7 in H8. lia. auto.
    -- rewrite H5. assert (H6 : max_list_Z l' >= h) by (induction l'; simpl in *; lia).
       pose proof (max_list_ge_not_in' l' h) as H7. assert (H8 : max_list_Z l' > 0) by lia. apply H7 in H8. 2 : { tauto. }
       assert (Z.of_nat (length l') = max_list_Z l' \/ Z.of_nat (length l') < max_list_Z l') as [H9 | H9].
       --- lia.
       --- rewrite <- H5 in H9. assert (NoDup (h :: l')) as H10 by (apply NoDup_cons; auto).
           assert (Z.of_nat (length l') = max_list_Z l' \/ Z.of_nat (length l') < max_list_Z l') as [H11 | H11] by lia.
           2 : { lia. } apply in_list_1 in H11.
           + rewrite Forall_forall in H1'. specialize (H1' 1). apply H1' in H11. lia.
           + lia.
           + apply H3.
           + assert (H12 : Forall (fun x : Z => x > 1) l' -> Forall (fun x : Z => x > 0) l').
             { intros H12. rewrite Forall_forall in H12. rewrite Forall_forall. intros x H13. apply H12 in H13. lia. }
             tauto.
      --- lia.
Qed.

Lemma max_primes_ge_len : forall l,
  first_n_primes l -> max_list_Z l >= Z.of_nat (length l).
Proof.
  intros l H1. pose proof Znt.prime_ge_2 as H2.
  pose proof (Znt.not_prime_1) as H3. assert (H4 : ~ In 1 l).
  { intros H4. unfold first_n_primes in H1. destruct H1 as [H1 [H5 H6]]. unfold prime_list in H5.
    rewrite Forall_forall in H5. specialize (H5 1). apply H5 in H4. tauto. }
  unfold first_n_primes in H1. destruct H1 as [H1 [H5 H6]]. unfold prime_list in H5. rewrite Forall_forall in H5.
  apply Z.le_ge. apply list_len_lt_max. split. rewrite Forall_forall. intros x H7. specialize (H5 x). apply H5 in H7.
  apply Znt.prime_ge_2 in H7. lia. apply H1.
Qed.

Lemma prime_in_first_n_primes : forall p,
  Znt.prime p -> exists l, first_n_primes l /\ In p l.
Proof.
  intros p H1. pose proof (prime_list_len (Z.to_nat p)) as [l [H2 H3]].
  exists l. split.
  - apply H2.
  - apply H2. apply max_primes_ge_len in H2. rewrite H3 in H2. rewrite Z2Nat.id in H2.
    2 : { apply Znt.prime_ge_2 in H1. lia. }
    split. apply H1. lia.
Qed.

Lemma gt_max_gt_all : forall (l : list Z) x1 x2,
  In x1 l -> x2 > max_list_Z l -> x2 > x1.
Proof.
  intros l x1 x2 H1 H2. induction l as [| h l' IH].
  - inversion H1.
  - simpl in H1. simpl in H2. destruct H1 as [H1 | H1].
    -- lia.
    -- apply IH. apply H1. lia.
Qed.

Theorem theorem_19_14_b : forall p1,
  Znt.prime p1 -> exists p2, Znt.prime p2 /\ p2 > p1.
Proof.
  intros p1 H1.
  apply prime_in_first_n_primes in H1 as [l [H1 H2]].
  pose proof (theorem_19_14_a l H1) as [p2 [H3 H4]]. exists p2. split.
  - apply H3.
  - apply gt_max_gt_all with (l := l); tauto.
Qed.

Lemma exists_prime_list : exists l,
  prime_list l /\ NoDup l /\ (length l > 0)%nat.
Proof.
  exists [2]. repeat split.
  - unfold prime_list. rewrite Forall_forall. intros x H1. destruct H1 as [H1 | H1]; subst.
    -- apply Znt.prime_2.
    -- inversion H1.
  - repeat constructor. intros H1. inversion H1.
  - simpl. lia.
Qed.

Lemma prime_factorization_exists : forall z : Z,
  z > 1 -> exists l : list Z,
    prime_list l /\ z = fold_right Z.mul 1 l.
Proof.
  intros z. assert (z <= 1 \/ z > 1) as [H1 | H1]; try lia.
  apply strong_induction_Z with (n := z); try lia.
  intros n IH H2. assert (n = 2 \/ n > 2) as [H3 | H3] by lia.
  - exists [2]. split; simpl; auto. right; auto. apply Znt.prime_2.
  - destruct (Znt.prime_dec n) as [H4 | H4].
    + exists [n]. split; simpl; try lia; constructor; auto.
    + rewrite <- Znt.prime_alt in H4. unfold Znt.prime' in H4. apply not_and_or in H4 as [H4 | H4]; try lia.
      apply not_all_ex_not in H4 as [p H4]. apply imply_to_and in H4 as [H4 H5].
      apply NNPP in H5. destruct H5 as [k H5]. assert (p > 1 /\ 0 <= p < n) as [H7 H8] by lia.
      assert (k > 1 /\ 0 <= k < n) as [H9 H10] by nia.
      assert (exists l1 : list Z, prime_list l1 /\ p = fold_right Z.mul 1 l1) as [l1 H11] by (apply IH; lia).
      assert (exists l2 : list Z, prime_list l2 /\ k = fold_right Z.mul 1 l2) as [l2 H12] by (apply IH; lia).
      exists (l1 ++ l2). split.
      -- apply Forall_app. split; [apply H11 | apply H12].
      -- destruct H11 as [H11 H13]. destruct H12 as [H12 H14]. rewrite fold_right_app. rewrite <- H14.
        rewrite fold_right_mul_distributive. rewrite <- H13. lia.
Qed.


Lemma prime_list_product_exists_pos : forall z,
  z > 1 -> exists l : list Z,
    prime_list l /\ z = fold_right Z.mul 1 l.
Proof.
  intros z H1. pose proof (prime_factorization_exists z) as H2. apply H2 in H1. destruct H1 as [l [H1 H3]]; exists l; split; auto; try lia.
Qed.

Lemma prime_list_product_exists_neg : forall z,
  z < -1 -> exists l : list Z,
    prime_list l /\ z = -fold_right Z.mul 1 l.
Proof.
  intros z H1. pose proof (prime_factorization_exists (-z)) as H2. assert (-z > 1) as H3 by lia.
  apply H2 in H3. destruct H3 as [l [H3 H4]]; exists l; split; auto; try lia.
Qed.

Lemma fold_right_mult_app_Z : forall l1 l2,
  fold_right Z.mul 1 (l1 ++ l2) = fold_right Z.mul 1 l1 * fold_right Z.mul 1 l2.
Proof.
  intros l1 l2. induction l1 as [| h1 t1 IH].
  - replace (fold_right Z.mul 1 []) with 1 by reflexivity. replace ([] ++ l2) with l2 by reflexivity. lia.
  - simpl. rewrite IH. lia.
Qed.

Lemma z_square_even_primes : forall z,
  (z > 1)%Z -> exists l, prime_list l /\ z^2 = fold_right Z.mul 1 l /\ (forall p, Nat.Even (count_occ Z.eq_dec l p)).
Proof.
  intros z H1. pose proof (prime_factorization_exists z H1) as [l [H2 H3]].
  exists (l ++ l). repeat split.
  - apply Forall_app; split; auto.
  - rewrite fold_right_mult_app_Z. lia.
  - intros p. rewrite count_occ_app. exists (count_occ Z.eq_dec l p). lia.
Qed.

Fixpoint reduce_freq_to_half {A : Type} (eq_dec : forall (x y : A), {x = y} + {x <> y})
                                      (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => 
      let freq := count_occ eq_dec l x in
      repeat x (Nat.div2 freq) ++ remove eq_dec x (reduce_freq_to_half eq_dec xs)
  end.  

Fixpoint reduce_freq_by_factor {A : Type} (eq_dec : forall (x y : A), {x = y} + {x <> y})
                                (k : nat) (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs =>
      let freq := count_occ eq_dec l x in
      repeat x (freq / k) ++ remove eq_dec x (reduce_freq_by_factor eq_dec k xs)
  end.

Lemma count_occ_remove_eq : forall h t,
  count_occ Z.eq_dec (remove Z.eq_dec h t) h = 0%nat.
Proof.
  intros h t. induction t as [| h' t' IH].
  - simpl. reflexivity.
  - simpl. destruct (Z.eq_dec h h') as [H1 | H1].
    + rewrite H1. simpl. destruct (Z.eq_dec h h) as [H2 | H2]; try lia. rewrite H1 in IH. apply IH.
    + simpl. destruct (Z.eq_dec h' h) as [H2 | H2]; try lia.
Qed.

Lemma count_occ_remove_neq : forall h t z,
  h <> z -> count_occ Z.eq_dec (remove Z.eq_dec h t) z = count_occ Z.eq_dec t z. 
Proof.
  intros h t z H1. induction t as [| h' t' IH].
  - simpl. reflexivity.
  - simpl. repeat (simpl; destruct (Z.eq_dec h h') as [H2 | H2]); repeat (simpl; destruct (Z.eq_dec h' z) as [H3 | H3]); try lia.
Qed.

Lemma count_occ_reduce_freq_not_in : forall l1 z,
  ~In z l1 -> count_occ Z.eq_dec (reduce_freq_to_half Z.eq_dec l1) z = 0%nat.
Proof.
  intros l1 z H1. induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl in H1. apply not_in_cons in H1 as [H1 H1']. simpl. destruct (Z.eq_dec h z) as [H2 | H2].
    + rewrite H2 in H1. contradiction.
    + rewrite count_occ_app. simpl. rewrite count_occ_repeat_neq; auto. rewrite count_occ_remove_neq; auto.
Qed.

Lemma count_occ_reduce_freq_to_half : forall l z,
  (Nat.div2 (count_occ Z.eq_dec l z) = count_occ Z.eq_dec (reduce_freq_to_half Z.eq_dec l) z)%nat.
Proof.
  intros l z. assert (In z l \/ ~In z l) as [H1 | H1] by apply classic.
  2 : { rewrite count_occ_reduce_freq_not_in; auto. apply (count_occ_not_In Z.eq_dec) in H1; auto. rewrite H1. reflexivity. }
  induction l as [| h t IH].
  - inversion H1.
  - destruct H1 as [H1 | H1].
    + rewrite H1. simpl. destruct (Z.eq_dec z z) as [H2 | H2]; try lia. rewrite count_occ_app. rewrite count_occ_repeat_eq; auto.
      rewrite count_occ_remove_eq. lia.
    + pose proof H1 as H1'. apply IH in H1. destruct (Z.eq_dec h z) as [H2 | H2].
      * rewrite H2. simpl. destruct (Z.eq_dec z z) as [H3 | H3]; try lia. rewrite count_occ_app. rewrite count_occ_repeat_eq; auto.
        rewrite count_occ_remove_eq. lia.
      * simpl. destruct (Z.eq_dec h z) as [H3 | H3]; destruct (Z.eq_dec h h) as [H4 | H4]; try lia.
        rewrite H1. simpl. rewrite count_occ_app. rewrite count_occ_repeat_neq; auto. rewrite count_occ_remove_neq; auto.
Qed.

Lemma count_occ_even_eq_app_reduce_freq_to_half : forall l1 l2,
  (forall z, Nat.Even (count_occ Z.eq_dec l1 z)) -> (l2 = reduce_freq_to_half Z.eq_dec l1) ->
  (forall z, (count_occ Z.eq_dec l1 z = count_occ Z.eq_dec (l2 ++ l2) z)%nat).
Proof.
  intros l1 l2 H1 H2 z. rewrite H2. rewrite count_occ_app. repeat rewrite <- count_occ_reduce_freq_to_half. 
  specialize (H1 z). destruct H1 as [n H1]. rewrite H1. rewrite div2_double. lia.
Qed.

Lemma fold_right_0_In : forall l,
  In 0 l -> fold_right Z.mul 1 l = 0.
Proof.
  intros l H1. induction l as [| h t IH].
  - inversion H1.
  - simpl. destruct H1 as [H1 | H1].
    + rewrite H1. lia.
    + apply IH in H1. lia.
Qed.

Lemma in_remove_in : forall a b l,
  In a (remove_one Z.eq_dec b l) -> In a l.
Proof.
  intros a b l H1. induction l as [| h t IH].
  - contradiction.
  - simpl in H1. destruct (Z.eq_dec h b) as [H2 | H2].
    + simpl. tauto.
    + simpl. destruct H1 as [H1 | H1].
      * left. auto.
      * tauto.
Qed.

Lemma remove_one_not_in_remove_one : forall (a b : Z) l,
  ~In a l -> ~In a (remove_one Z.eq_dec b l).
Proof.
  intros a b l H1 H2. apply H1. apply in_remove_in in H2. auto.
Qed.

Lemma in_div_fold_right : forall l z,
  In z l -> (z | fold_right Z.mul 1 l).
Proof.
  intros l z H. induction l as [| h t IH].
  - inversion H.
  - simpl. destruct H as [H | H].
    -- rewrite H. apply Z.divide_factor_l.
    -- apply IH in H. destruct H as [r H]. exists (r * h). lia.
Qed.

Lemma not_in_0_fold_right_neq_0 : forall l,
  ~In 0 l -> fold_right Z.mul 1 l <> 0.
Proof.
  intros l H1. induction l as [| h t IH].
  - simpl. lia.
  - simpl. apply not_in_cons in H1 as [H1 H1']. destruct (Z.eq_dec h 0) as [H2 | H2].
    + rewrite H2. lia.
    + apply IH in H1'. lia.
Qed.

Lemma fold_right_remove_one_In : forall a l,
  ~In 0 l -> In a l -> fold_right Z.mul 1 (remove_one Z.eq_dec a l) = fold_right Z.mul 1 l / a.
Proof.
  intros a l H1 H2. induction l as [| h t IH].
  - inversion H2.
  - simpl. destruct (Z.eq_dec h a) as [H3 | H3].
    + rewrite H3. replace (a * fold_right Z.mul 1 t / a) with (fold_right Z.mul 1 t).
      2 : { rewrite <- Z.mul_comm. rewrite Z.div_mul; auto. apply not_in_cons in H1. lia. }
      lia.
    + simpl. destruct H2 as [H2 | H2]; try contradiction.
      rewrite IH; auto. 2 : { apply not_in_cons in H1. tauto. }
      apply in_div_fold_right in H2 as [r H2]. rewrite H2. rewrite Z.div_mul. 
      2 : { apply not_in_cons in H1 as [H1 H1']. apply not_in_0_fold_right_neq_0 in H1'. lia. }
      rewrite Z.mul_assoc. rewrite Z.div_mul; auto. apply not_in_cons in H1. 
      destruct H1 as [H1 H1']. apply not_in_0_fold_right_neq_0 in H1'. lia.
Qed.

Lemma count_occ_equ_fold_right : forall l1 l2,
  (forall z, (count_occ Z.eq_dec l2 z = count_occ Z.eq_dec l1 z)%nat) ->
  fold_right Z.mul 1 l1 = fold_right Z.mul 1 l2.
Proof.
  intros l1 l2 H1. assert (In 0 l2 \/ ~In 0 l2) as [H0 | H0] by apply classic.
  - specialize (H1 0). assert (In 0 l1). { apply (count_occ_In Z.eq_dec) in H0. apply (count_occ_In Z.eq_dec). lia. }
    repeat rewrite fold_right_0_In; auto.
  - assert (H0' : ~In 0 l1). { intros H2. apply H0. apply (count_occ_In Z.eq_dec) in H2. apply (count_occ_not_In Z.eq_dec) in H0. specialize (H1 0). lia. } 
    generalize dependent l2. induction l1 as [| h t IH].
    intros l2 H1. simpl in *. apply count_occ_inv_nil in H1. rewrite H1. reflexivity.
  -- intros l2 H1 H2. simpl. simpl in H0'. apply not_or_and in H0' as [H0' H0'']. specialize (IH H0'' (remove_one Z.eq_dec h l2)). rewrite IH.
    2 : { 
      intros z. assert (In z l2 \/ ~In z l2) as [H3 | H3] by apply classic.
      - assert (h = z \/ h <> z) as [H4 | H4] by apply classic.
         + rewrite H4 in *. specialize (H1 z). rewrite count_occ_cons_eq in H1; auto. rewrite remove_one_In; auto. lia.
         + specialize (H1 z). rewrite count_occ_cons_neq in H1; auto. rewrite <- H1. rewrite count_occ_remove_one_not_eq; auto.
       - assert (h = z \/ h <> z) as [H4 | H4] by apply classic.
         + rewrite H4 in *. specialize (H1 z). apply (count_occ_not_In Z.eq_dec) in H3. rewrite H3 in H1. rewrite count_occ_cons_eq in H1; auto. lia.
         + specialize (H1 z). rewrite count_occ_cons_neq in H1; auto. rewrite <- H1. rewrite count_occ_remove_one_not_eq; auto.
    }
    2 : { intros H3. apply (remove_one_not_in_remove_one 0 h l2) in H2. tauto. }
    specialize (H1 h). rewrite count_occ_cons_eq in H1; auto. assert (In h l2) as H3.
    { rewrite (count_occ_In Z.eq_dec). lia. } rewrite fold_right_remove_one_In; auto. apply in_div_fold_right in H3 as [r H3]. rewrite H3. rewrite Z.div_mul; auto; lia.
Qed.

Lemma fold_right_even_square : forall l1,
    (forall z, Nat.Even (count_occ Z.eq_dec l1 z)) -> exists l2,
    fold_right Z.mul 1 l1 = (fold_right Z.mul 1 l2)^2.
Proof.
  intros l1 H1. set (l2 := reduce_freq_to_half Z.eq_dec l1). exists (l2).
  pose proof (count_occ_even_eq_app_reduce_freq_to_half l1 l2 H1 eq_refl) as H2. 
  apply count_occ_equ_fold_right in H2. rewrite <- H2. rewrite fold_right_mult_app_Z. nia. 
Qed.

Lemma even_count_occ_perfect_square : forall z,
  (exists l, z = fold_right Z.mul 1 l /\ (forall p, Nat.Even (count_occ Z.eq_dec l p))) ->
    (exists m, z = m^2).
Proof.
  intros z [l [H1 H2]]. pose proof (fold_right_even_square l H2) as H3.
  destruct H3 as [l2 H3]. exists (fold_right Z.mul 1 l2). rewrite H1. rewrite H3. reflexivity.
Qed.

Lemma prime_factorization_unique : forall l1 l2 z p,
  prime_list l1 -> prime_list l2 -> z = fold_right Z.mul 1 l1 -> z = fold_right Z.mul 1 l2 -> 
  count_occ Z.eq_dec l1 p = count_occ Z.eq_dec l2 p.
Proof.
  intros l1 l2 z p H1 H2 H3 H4.
  pose proof (lt_eq_lt_dec (count_occ Z.eq_dec l1 p) (count_occ Z.eq_dec l2 p)) as [[H5 | H5] | H5].
  2 : { auto. }
  - assert (H6 : In p l2). { apply (count_occ_In Z.eq_dec); lia. } pose proof (count_mul_div_fold_right l2 p H6) as H7.
    rewrite <- H4 in H7. assert (count_occ Z.eq_dec l1 p = 0 \/ count_occ Z.eq_dec l1 p > 0)%nat as [H8 | H8] by lia.
    -- assert (H9 : ~In p l1). { intros H9. apply (count_occ_not_In Z.eq_dec) in H9. lia. lia. } 
       assert (H10 : ~(p | fold_right Z.mul 1 l1)). { apply p_notin_ndiv_fold_right; auto. apply in_prime_list in H6; auto. }
       rewrite <- H3 in H10. assert (H11 : (p | z)). { apply z_pow_div_z_div with (c := Z.of_nat (count_occ Z.eq_dec l2 p)); auto; lia. } tauto.
    -- assert (H9 : In p l1). { apply (count_occ_In Z.eq_dec); lia. } pose proof (count_mul_div_fold_right l1 p H9) as H10.
       rewrite <- H3 in H10. assert (H11 : (p | z / p ^ (Z.of_nat (count_occ Z.eq_dec l1 p)))).
       { destruct H7 as [r1 H7]. destruct H10 as [r2 H10]. exists (r1 * p ^ Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p - 1)). rewrite H10. rewrite Z.div_mul. 
         2 : { apply Z.pow_nonzero. apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6. lia. lia. }
         rewrite <- Z.mul_assoc. rewrite Z.mul_comm with (m := p). rewrite <- Z.pow_succ_r; try lia.
         replace (Z.succ (Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p - 1))) with (Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p)) by lia.
         rewrite Nat2Z.inj_sub; try lia. rewrite Z.pow_sub_r; try lia. 2 : { apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6. lia. }
         assert (H12 : (p ^ Z.of_nat (count_occ Z.eq_dec l1 p) | p ^ Z.of_nat (count_occ Z.eq_dec l2 p))). 
         { exists (p ^ (Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p))). rewrite z_pow_mult; try lia. 
           2 : { apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6. lia. }
           replace (Z.of_nat (count_occ Z.eq_dec l2 p - count_occ Z.eq_dec l1 p) + Z.of_nat (count_occ Z.eq_dec l1 p)) with (Z.of_nat (count_occ Z.eq_dec l2 p)) by lia. lia. 
         }
         rewrite z_mul_div; auto. 2 : { apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6. lia. }
         rewrite <- H7. rewrite H10. rewrite Z.div_mul; auto. apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6. lia.
       }
       pose proof p_ndiv_fold_right l1 p H1 H9 as H12. rewrite <- H3 in H12. tauto.
  - assert (H6 : In p l1). { apply (count_occ_In Z.eq_dec); lia. } pose proof (count_mul_div_fold_right l1 p H6) as H7.
    rewrite <- H3 in H7. assert (count_occ Z.eq_dec l2 p = 0 \/ count_occ Z.eq_dec l2 p > 0)%nat as [H8 | H8] by lia.
    -- assert (H9 : ~In p l2). { intros H9. apply (count_occ_not_In Z.eq_dec) in H9. lia. lia. } 
       assert (H10 : ~(p | fold_right Z.mul 1 l2)). { apply p_notin_ndiv_fold_right; auto. apply in_prime_list in H6; auto. }
       rewrite <- H4 in H10. assert (H11 : (p | z)). { apply z_pow_div_z_div with (c := Z.of_nat (count_occ Z.eq_dec l1 p)); auto; lia. }
       tauto.
    -- assert (H9 : In p l2). { apply (count_occ_In Z.eq_dec); lia. } pose proof (count_mul_div_fold_right l2 p H9) as H10.
       rewrite <- H4 in H10. assert (H11 : (p | z / p ^ (Z.of_nat (count_occ Z.eq_dec l2 p)))).
       { destruct H7 as [r1 H7]. destruct H10 as [r2 H10]. exists (r1 * p ^ Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p - 1)). rewrite H10. rewrite Z.div_mul.
         2 : { apply Z.pow_nonzero. apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6. lia. lia. }
         rewrite <- Z.mul_assoc. rewrite Z.mul_comm with (m := p). rewrite <- Z.pow_succ_r; try lia.
         replace (Z.succ (Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p - 1))) with (Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p)) by lia.
         rewrite Nat2Z.inj_sub; try lia. rewrite Z.pow_sub_r; try lia. 2 : { apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6. lia. }
         assert (H12 : (p ^ Z.of_nat (count_occ Z.eq_dec l2 p) | p ^ Z.of_nat (count_occ Z.eq_dec l1 p))). 
         { exists (p ^ (Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p))). rewrite z_pow_mult; try lia. 
           2 : { apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6. lia. }
           replace (Z.of_nat (count_occ Z.eq_dec l1 p - count_occ Z.eq_dec l2 p) + Z.of_nat (count_occ Z.eq_dec l2 p)) with (Z.of_nat (count_occ Z.eq_dec l1 p)) by lia. lia. 
         }
         rewrite z_mul_div; auto. 2 : { apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6. lia. }
         rewrite <- H7. rewrite H10. rewrite Z.div_mul; auto. apply in_prime_list in H6; auto. apply Znt.prime_ge_2 in H6. lia.
       }
       pose proof p_ndiv_fold_right l2 p H2 H9 as H12. rewrite <- H4 in H12. tauto.
Qed.

Fixpoint repeat_app (l : list Z) (n : nat) : list Z :=
  match n with
  | O => []
  | S n' => l ++ repeat_app l n'
  end. 

Lemma in_repeat_app : forall l n z,
  In z (repeat_app l n) -> In z l.
Proof.
  intros l n z H. induction n as [| n' IH].
  - simpl in H. contradiction.
  - simpl in H. apply in_app_or in H. destruct H as [H | H]; auto.
Qed.

Lemma count_occ_repeat_app : forall l n z,
  count_occ Z.eq_dec (repeat_app l n) z = (n * count_occ Z.eq_dec l z)%nat.
Proof.
  intros l n z. induction n as [| n' IH].
  - simpl. lia.
  - simpl. rewrite count_occ_app. rewrite IH. lia.
Qed.

Lemma count_occ_repeat_eq : forall n z,
  count_occ Z.eq_dec (repeat z n) z = n.
Proof.
  intros n z. induction n as [| n' IH].
  - simpl. lia.
  - simpl. destruct (Z.eq_dec z z) as [H1 | H1].
    + rewrite IH. lia.
    + contradiction.
Qed.

Lemma count_occ_repeat_possible_equal : forall h n z,
  count_occ Z.eq_dec (repeat h n) z = (if Z.eq_dec h z then n else 0)%nat.
Proof.
  intros h n z. induction n as [| n' IH].
  - simpl. destruct (Z.eq_dec h z); lia.
  - simpl. destruct (Z.eq_dec h z) as [H1 | H1].
    + rewrite H1 in *. lia.
    + apply IH.
Qed.

Lemma count_occ_2n_exist_app : forall l1 l2 n,
  (forall z, (count_occ Z.eq_dec l2 z = 2 * n * count_occ Z.eq_dec l1 z)%nat) ->
    exists l3, forall z, (count_occ Z.eq_dec l2 z = count_occ Z.eq_dec (l3 ++ l3) z)%nat.
Proof.
  intros l1 l2 n H1. destruct l1 as [| h t].
  - exists l2. intros z. simpl in H1. rewrite Nat.mul_0_r in H1. apply count_occ_inv_nil in H1. rewrite H1. reflexivity.
  - exists (repeat h n ++ repeat_app t n). intros z. specialize (H1 z). rewrite H1. repeat rewrite count_occ_app. 
    repeat rewrite count_occ_repeat_app. destruct (Z.eq_dec h z) as [H2 | H2].
    -- rewrite H2. repeat rewrite count_occ_repeat_eq. simpl. destruct (Z.eq_dec z z) as [H3 | H3]; try contradiction. lia.
    -- repeat rewrite count_occ_repeat_possible_equal. destruct (Z.eq_dec z h) as [H3 | H3].
       + rewrite H3. simpl. destruct (Z.eq_dec h h) as [H4 | H4]; try contradiction. lia.
       + destruct (Z.eq_dec h z) as [H4 | H4]; try contradiction. simpl. 
         destruct (Z.eq_dec h z) as [H5 | H5]; try contradiction. lia.
Qed.

Lemma repeat_app_nil : forall (l : list Z) n,
  repeat_app [] n = [].
Proof.
  intros l n. induction n as [| n' IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma fold_right_repeat_app : forall l n,
  fold_right Z.mul 1 (repeat_app l n) = fold_right Z.mul 1 l ^ Z.of_nat n.
Proof.
  intros l n. induction n as [| n' IH].
  - simpl. lia.
  - replace (fold_right Z.mul 1 (repeat_app l (S n'))) with (fold_right Z.mul 1 (l ++ repeat_app l n')) by reflexivity.
    rewrite fold_right_mult_app_Z. rewrite IH. rewrite <- Z.pow_succ_r; lia.
Qed.

Lemma z_pow_factor_primes : forall z k,
  (z > 1)%Z -> exists l, prime_list l /\ z^Z.of_nat k = fold_right Z.mul 1 l /\ (forall p, exists q, (count_occ Z.eq_dec l p) = q * k)%nat.
Proof.
  intros z k H1. pose proof (prime_factorization_exists z H1) as [l [H2 H3]].
  exists (repeat_app l k). repeat split.
  - apply Forall_forall. intros x H4. apply in_repeat_app in H4. apply in_prime_list in H4; auto.
  - rewrite fold_right_repeat_app. rewrite H3. lia.
  - intros p. rewrite count_occ_repeat_app. exists (count_occ Z.eq_dec l p). lia.
Qed.

Lemma count_occ_reduce_freq_to_half_prime : forall l z,
  (count_occ Z.eq_dec l z / 2 = count_occ Z.eq_dec (reduce_freq_to_half Z.eq_dec l) z)%nat.
Proof.
  intros l z. pose proof (count_occ_reduce_freq_to_half l z) as H1. rewrite Nat.div2_div in H1. apply H1.
Qed.

Lemma count_occ_reduce_freq_factor_not_in : forall l1 z k,
  ~In z l1 -> count_occ Z.eq_dec (reduce_freq_by_factor Z.eq_dec k l1) z = 0%nat.
Proof.
  intros l1 z k H1. induction l1 as [| h t IH].
  - simpl. reflexivity.
  - simpl in H1. apply not_in_cons in H1 as [H1 H1']. simpl. destruct (Z.eq_dec h z) as [H2 | H2].
    + rewrite H2 in H1. contradiction.
    + rewrite count_occ_app. simpl. rewrite count_occ_repeat_neq; auto. rewrite count_occ_remove_neq; auto.
Qed.

Lemma count_occ_reduce_freq_by_factor : forall l z k,
  (count_occ Z.eq_dec l z / k = count_occ Z.eq_dec (reduce_freq_by_factor Z.eq_dec k l) z)%nat.
Proof.
  intros l z k. assert (In z l \/ ~In z l) as [H1 | H1] by apply classic.
  2 : { rewrite count_occ_reduce_freq_factor_not_in; auto. apply (count_occ_not_In Z.eq_dec) in H1; auto. rewrite H1. apply Nat.Div0.div_0_l. }
  induction l as [| h t IH].
  - inversion H1.
  - destruct H1 as [H1 | H1].
    + rewrite H1. simpl. destruct (Z.eq_dec z z) as [H2 | H2]; try lia. simpl. rewrite count_occ_app. rewrite count_occ_repeat_eq.
      rewrite count_occ_remove_eq. lia.
    + pose proof H1 as H1'. apply IH in H1. destruct (Z.eq_dec h z) as [H2 | H2].
      * rewrite H2. simpl. destruct (Z.eq_dec z z) as [H3 | H3]; try lia. simpl. rewrite count_occ_app. rewrite count_occ_repeat_eq.
        rewrite count_occ_remove_eq. lia.
      * simpl. destruct (Z.eq_dec h z) as [H3 | H3]; destruct (Z.eq_dec h h) as [H4 | H4]; try lia.
        rewrite H1. simpl. rewrite count_occ_app. rewrite count_occ_repeat_neq; auto. rewrite count_occ_remove_neq; auto.
Qed.

Lemma count_occ_reduce_freq_by_factor_prime : forall l z k,
  (count_occ Z.eq_dec l z / k = count_occ Z.eq_dec (reduce_freq_by_factor Z.eq_dec k l) z)%nat.
Proof.
  intros l z k. pose proof (count_occ_reduce_freq_by_factor l z k) as H1. apply H1.
Qed.

Lemma count_occ_even_eq_app_reduce_freq_by_factor : forall l1 l2 k,
  (forall z, (exists q, (count_occ Z.eq_dec l1 z) = q * k)%nat) -> (l2 = reduce_freq_by_factor Z.eq_dec k l1) ->
  (forall z, (count_occ Z.eq_dec l1 z = count_occ Z.eq_dec (repeat_app l2 k) z)%nat).
Proof.
  intros l1 l2 k H1 H2 z. rewrite H2. rewrite count_occ_repeat_app. repeat rewrite <- count_occ_reduce_freq_by_factor. 
  specialize (H1 z). destruct H1 as [q H1]. rewrite H1. assert (k = 0 \/ k <> 0)%nat as [H3 | H3] by lia.
  - rewrite H3. simpl. lia.
  - rewrite Nat.div_mul; lia.
Qed.

Lemma fold_right_mult_repeat_app_Z : forall l n,
  fold_right Z.mul 1 (repeat_app l n) = fold_right Z.mul 1 l ^ (Z.of_nat n).
Proof.
  intros l n. induction n as [| n' IH].
  - simpl. lia.
  - replace (fold_right Z.mul 1 (repeat_app l (S n'))) with (fold_right Z.mul 1 (l ++ repeat_app l n')) by reflexivity. rewrite fold_right_mult_app_Z. rewrite IH.
    rewrite Nat2Z.inj_succ. rewrite Z.pow_succ_r. 2 : { lia. } lia.  
Qed.

Lemma fold_right_factor : forall l1 k,
  (forall z, (exists q, (count_occ Z.eq_dec l1 z) = q * k)%nat) -> exists l2,
  fold_right Z.mul 1 l1 = (fold_right Z.mul 1 l2)^Z.of_nat k.
Proof.
  intros l1 k H1. set (l2 := reduce_freq_by_factor Z.eq_dec k l1). exists (l2).
  pose proof (count_occ_even_eq_app_reduce_freq_by_factor l1 l2 k H1 eq_refl) as H2. 
  apply count_occ_equ_fold_right in H2. rewrite <- H2. rewrite fold_right_mult_repeat_app_Z. reflexivity.
Qed.

Lemma count_occ_perfect_factor : forall z k,
  (exists l, z = fold_right Z.mul 1 l /\ (forall p, (exists q, (count_occ Z.eq_dec l p) = q * k)%nat)) ->
    (exists m, z = m^Z.of_nat k).
Proof.
  intros z k [l [H1 H2]]. pose proof (fold_right_factor l k H2) as H3.
  destruct H3 as [l2 H3]. exists (fold_right Z.mul 1 l2). rewrite H1. rewrite H3. reflexivity.
Qed.

Lemma prime_divides : forall z,
  z > 1 -> (exists p, Znt.prime' p /\ (p | z)).
Proof.
  intros z. assert (z <= 1 \/ z > 1) as [H1 | H1] by lia.
  - lia.
  - apply strong_induction_Z with (n := z). 2 : { lia. }
    intros n IH H2. assert (n = 2 \/ n > 2) as [H3 | H3] by lia.
    + exists 2. split.
      * rewrite Znt.prime_alt. apply Znt.prime_2.
      * exists (1). lia.
    + destruct (Znt.prime_dec n) as [H4 | H4].
      * exists n. split.
        -- rewrite Znt.prime_alt. auto.
        -- exists (1). lia.
      * rewrite <- Znt.prime_alt in H4. unfold Znt.prime' in H4. apply not_and_or in H4. destruct H4 as [H4 | H4].
        -- lia.
        -- apply not_all_ex_not in H4. destruct H4 as [p H4]. apply imply_to_and in H4. destruct H4 as [H4 H5].
           assert (p <= n) as H6 by lia. assert (p > 1) as H7 by lia. apply NNPP in H5. assert (0 <= p < n) as H9 by lia.
           specialize (IH p H9 H7). destruct IH as [p' IH]. exists p'. split.
            ++ apply IH.
            ++ apply div_trans with (b := p); (try apply IH; try apply H5).
Qed.

Lemma prime_divides_2 : forall z,
  (z < -1 \/ z > 1) -> (exists p, Znt.prime' p /\ (p | z)).
Proof.
  intros z [H1 | H2]. 
  - pose proof prime_divides (-z) as H3. assert (-z > 1) as H4 by lia. apply H3 in H4. destruct H4 as [p [H4 [r H5]]]. exists p. split; auto. exists (-r). lia.
  - apply prime_divides in H2. auto.
Qed.

Lemma prime_div_pow_div_Z : forall p a n,
  Znt.prime p -> (p | a ^ Z.of_nat n)%Z -> (p | a)%Z.
Proof.
  intros p a n H1 H2. induction n as [| k IH].
  - simpl in H2. destruct H2 as [b H2]. apply Znt.prime_alt in H1 as [H1 H1']. assert (b = 1)%Z as H3 by lia. lia.
  - replace (Z.of_nat (S k)) with (Z.succ (Z.of_nat k)) in H2 by lia. rewrite Z.pow_succ_r in H2; try lia. apply Znt.prime_mult in H2 as [H2 | H2]; auto.
Qed.