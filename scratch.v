From Lib Require Import Imports Reals_util Sums Continuity Limit Notations Products Polynomial.
Open Scope R_scope.
Import LimitNotations SumNotations.

Local Notation length := List.length.

Lemma sum_f_rev_index : forall n (f : nat -> R), sum_f 0 n f = sum_f 0 n (fun i => f (n - i)%nat).
Proof.
  intros n f. induction n as [|n IH].
  - rewrite sum_f_0_0, sum_f_0_0. replace (0 - 0)%nat with 0%nat by lia. reflexivity.
  - rewrite sum_f_i_Sn_f; try lia.
    rewrite sum_f_Si with (i := 0%nat) (f := fun i => f (S n - i)%nat); try lia.
    rewrite IH. f_equal. rewrite sum_f_reindex' with (s := 1%nat). 
    replace (0 + 1)%nat with 1%nat by lia. 
    replace (n + 1)%nat with (S n) by lia. 
    apply sum_f_equiv; try lia. 
    intros i Hi. f_equal. lia.
Qed.

Lemma sum_f_0_pow : forall n (f : nat -> R),
  sum_f 0 n (fun i => f i * 0 ^ (n - i)) = f n.
Proof.
  induction n as [| n IH].
  - intros f. rewrite sum_f_0_0. replace (0 - 0)%nat with 0%nat by lia.
    replace (0^0) with 1 by lra. lra.
  - intros f. rewrite sum_f_i_Sn_f; try lia.
    replace (S n - S n)%nat with 0%nat by lia.
    replace (0^0) with 1 by lra.
    assert (H_zero : sum_f 0 n (fun i : nat => f i * 0 ^ (S n - i)) = 0).
    {
      transitivity (sum_f 0 n (fun _ : nat => 0)).
      - apply sum_f_equiv; try lia. intros i Hi. 
        replace (S n - i)%nat with (S (n - i))%nat by lia.
        simpl. lra.
      - clear IH. induction n as [| n' IHn'].
        + rewrite sum_f_0_0. reflexivity.
        + rewrite sum_f_i_Sn_f; try lia. rewrite IHn'. lra.
    }
    rewrite H_zero. lra.
Qed.

Lemma poly_eval_0 : forall l, (length l > 0)%nat -> polynomial l 0 = nth (length l - 1) l 0.
Proof.
  intros l H.
  unfold polynomial.
  pose proof sum_f_0_pow (length l - 1) (fun i => nth i l 0) as H1.
  exact H1.
Qed.

Lemma rev_length_minus_1_nth : forall l (d : R),
  (length l > 0)%nat ->
  nth (length l - 1) (rev l) d = nth 0 l d.
Proof.
  intros l d H. rewrite rev_nth; try lia.
  replace (length l - S (length l - 1))%nat with 0%nat by lia. reflexivity.
Qed.

Lemma poly_rev_eval_eq : forall l x, x <> 0 ->
  (length l > 0)%nat ->
  polynomial (rev l) x = x ^ (length l - 1) * polynomial l (1/x).
Proof.
  intros l x Hx Hlen.
  unfold polynomial.
  rewrite length_rev.
  rewrite r_mult_sum_f_i_n_f_l.
  rewrite sum_f_rev_index.
  apply sum_f_equiv; try lia.
  intros i H.
  rewrite rev_nth; try lia.
  replace (length l - S (length l - 1 - i))%nat with i by lia.
  replace (length l - 1 - (length l - 1 - i))%nat with i by lia.
  replace (1 / x) with (/ x) by lra.
  first [ rewrite pow_inv; auto | rewrite pow_inv; auto ].
  replace (Datatypes.length l - 1)%nat with (i + (Datatypes.length l - 1 - i))%nat at 1 by lia.
  rewrite pow_add.
  field; auto; try apply pow_nonzero; auto.
Qed.

Lemma limit_poly_1_x : forall l, (length l > 0)%nat ->
  ⟦ lim 0 ⟧ (fun x => x ^ (length l - 1) * polynomial l (1/x)) = nth 0 l 0.
Proof.
  intros l Hlen.
  apply limit_eq with (f1 := polynomial (rev l)).
  - exists 1. split; [lra |]. intros x H. symmetry.
    assert (H1 : x <> 0) by solve_abs.
  unfold polynomial.
  rewrite length_rev.
  rewrite r_mult_sum_f_i_n_f_l.
  symmetry.
  rewrite sum_f_rev.
  symmetry.
  apply sum_f_equiv; try lia.
  intros i H2.
  rewrite rev_nth; try lia.
  replace (Datatypes.length l - 1 - (Datatypes.length l - 1 - i))%nat with i by lia.
  replace (1 / x) with (/ x) by lra.
  first [ rewrite pow_inv; auto | rewrite pow_inv; auto ].
  replace (Datatypes.length l - 1)%nat with (i + (Datatypes.length l - 1 - i))%nat at 1 by lia.
  rewrite pow_add.
  field_simplify; try apply pow_nonzero; auto.
  replace (length l - S (length l - 1 - i))%nat with i by lia. auto.
  - pose proof (continuous_polynomial (rev l) 0) as H1. 
    unfold continuous_at in H1.
    replace (nth 0 l 0) with (polynomial (rev l) 0).
  1: exact H1.
  unfold polynomial.
  rewrite length_rev.
  erewrite sum_single_index with (k := (length l - 1)%nat).
  + replace (length l - 1 - (length l - 1))%nat with 0%nat by lia.
    simpl. rewrite Rmult_1_r.
    rewrite rev_nth; try lia.
    replace (length l - S (length l - 1))%nat with 0%nat by lia.
    reflexivity.
  + lia.
  + intros j H2 H3.
    replace (length l - 1 - j)%nat with (S (length l - 1 - j - 1))%nat by lia.
    simpl. lra.
Qed.

Lemma poly_cons_0_eval : forall l x, polynomial (0 :: l) x = polynomial l x.
Proof.
  intros l x. rewrite poly_cons. simpl. 
  replace (length l) with (length l - 0)%nat by lia. 
  lra.
Qed.

Lemma limit_0_pow : forall k, (0 < k)%nat -> ⟦ lim 0 ⟧ (fun y => y ^ k) = 0.
Proof.
  induction k as [| k IH].
  - intros H; lia.
  - intros _. destruct (Nat.eq_dec k 0) as [H1 | H1].
    + subst k. simpl. replace (fun y => y * 1) with (fun y : R => y) by (extensionality y; lra).
      apply limit_id.
    + replace (S k) with (k + 1)%nat by lia. rewrite <- Nat.add_1_r.
      simpl. replace (fun y => y ^ (k + 1)) with (fun y => y * y ^ k). 
      2 : { extensionality y. replace (k + 1)%nat with (S k) by lia. rewrite tech_pow_Rmult. auto. }
      replace 0 with (0 * 0) at 2 by lra. apply limit_mult. apply limit_id. apply IH; lia.
Qed.

Lemma limit_poly_lead_coeff : forall l,
  ~ is_zero_poly l ->
  exists f, (forall x, x <> 0 -> f x = x ^ (degree l) * polynomial l (1/x)) /\
  ⟦ lim 0 ⟧ f = lead_coeff l.
Proof.
  induction l as [| h t IH].
  - intros H; exfalso; apply H; apply Forall_nil.
  - destruct (Req_EM_T h 0) as [Heq | Hneq].
    + subst h. intros Hnz.
      assert (Hnzt : ~ is_zero_poly t).
      { intros Ht. apply Hnz. apply Forall_cons; auto. }
      specialize (IH Hnzt) as [f [Hf Hlim]].
      exists f. split; auto.
      intros x Hx. rewrite Hf; auto.
      simpl. destruct (Req_EM_T 0 0); try lra.
      rewrite poly_cons_0_eval. reflexivity. simpl. destruct (Req_dec_T 0 0); [exact Hlim | lra].
    + intros Hnz.
      exists (fun x => x ^ (length (h::t) - 1) * polynomial (h::t) (1/x)).
      split.
      * intros x Hx. simpl. destruct (Req_EM_T h 0); try lra.
      * simpl. destruct (Req_EM_T h 0); try lra.
        replace (length t - 0)%nat with (length t)%nat by lia.
  apply limit_eq with (f1 := polynomial (rev (h :: t))).
  -- exists 1. split; [lra |].
    intros x Hx.
    unfold polynomial.
    rewrite length_rev.
    replace (length (h :: t) - 1)%nat with (length t)%nat by (simpl; lia).
    rewrite r_mult_sum_f_i_n_f_l.
    assert (sum_f_rev : forall n' f0, ∑ 0 n' f0 = ∑ 0 n' (fun i => f0 (n' - i)%nat)).
    {
      clear.
      induction n' as [| n' IH]; intros f0.
      - simpl. repeat rewrite sum_f_0_0; auto.
      - rewrite sum_f_i_Sn_f; try lia.
        rewrite IH.
        rewrite sum_f_Si with (i := 0%nat) (n := S n') (f := fun i => f0 (S n' - i)%nat); try lia.
        replace (f0 (S n' - 0)%nat) with (f0 (S n')) by (f_equal; lia).
        replace (∑ 0 n' (λ i : ℕ, f0 (n' - i)%nat) + f0 (S n')) with (f0 (S n') + ∑ 0 n' (λ i : ℕ, f0 (n' - i)%nat)) by lra.
        field_simplify.
        rewrite sum_f_reindex' with (s := 1%nat) (i := 0%nat) (n := n').
        replace (n' + 1)%nat with (S n') by lia.
        f_equal.
        apply sum_f_equiv; try lia.
        intros k Hk. f_equal. lia.
    }
    symmetry.
    rewrite sum_f_rev.
    symmetry.
    apply sum_f_equiv; try lia.
    intros i H2.
    rewrite rev_nth; try (simpl; lia).
    replace (length (h :: t) - 1 - i)%nat with (length t - i)%nat by (simpl; lia).
    replace (length t - (length t - i))%nat with i by lia.
    replace (1 / x) with (/ x) by lra.
    first [ rewrite pow_inv; auto | rewrite pow_inv; auto ].
    replace (length t)%nat with ((length t - i) + i)%nat at 1 by lia.
    field_simplify; try apply pow_nonzero; try solve [solve_R].
    replace (length t - i + i - i)%nat with (length t - i)%nat by lia.
    admit.
  -- replace h with (nth 0 (h :: t) 0) by reflexivity.
    replace (nth 0 (h :: t) 0) with (polynomial (rev (h :: t)) 0).
    ++ apply continuous_at_polynomial.
    + unfold polynomial.
      rewrite rev_length.
      replace (length (h :: t) - 1)%nat with (length t)%nat by (simpl; lia).
      erewrite sum_single_index with (k := (length t)%nat).
      * replace (length t - length t)%nat with 0%nat by lia.
        simpl. rewrite Rmult_1_r.
        rewrite rev_nth; try (simpl; lia).
        replace (length (h :: t) - 1 - length t)%nat with 0%nat by (simpl; lia).
        reflexivity.
      * lia.
      * intros j H2 H3.
        replace (length t - j)%nat with (S (length t - j - 1))%nat by lia.
        simpl. lra.
Admitted.

Lemma limit_eq_zero_mult : forall f g a,
  ⟦ lim a ⟧ f = 0 ->
  (exists M δ, δ > 0 /\ forall x, 0 < |x - a| < δ -> |g x| <= M) ->
  ⟦ lim a ⟧ (fun x => f x * g x) = 0.
Proof.
  intros f g a H1 [M [δ1 [Hδ1 Hbd]]] ε Heps.
  assert (H_M : M + 1 > 0).
  { pose proof (Rtotal_order 0 M) as [H | [H | H]]. lra. lra. 
    specialize (Hbd (a + δ1 / 2) ltac:(solve_abs)). solve_abs. }
  specialize (H1 (ε / (M + 1)) ltac:(apply Rdiv_pos_pos; lra)) as [δ2 [Hδ2 Hf]].
  exists (Rmin δ1 δ2). split; [solve_min |].
  intros x Hx.
  specialize (Hbd x ltac:(solve_min)).
  specialize (Hf x ltac:(solve_min)).
  replace (f x * g x - 0) with (f x * g x) by lra.
  rewrite Rabs_mult.
  assert (|f x| < ε / (M + 1)) by solve_abs.
  assert (|g x| < M + 1) by lra.
  assert (|f x| * |g x| < (ε / (M + 1)) * (M + 1)).
  { apply Rmult_le_0_lt_compat; try solve_abs; nra. }
  replace (ε / (M + 1) * (M + 1)) with ε in H1 by (field; lra).
  exact H1.
Qed.

Lemma bounded_poly_1_x : forall l,
  exists M δ, δ > 0 /\ forall x, 0 < |x - 0| < δ -> |x ^ (degree l) * polynomial l (1/x)| <= M.
Proof.
  intros l.
  destruct (is_zero_poly_dec l) as [Hz | Hnz].
  - exists 0, 1. split; [lra |]. intros x Hx.
    pose proof (is_zero_poly_eval l (1/x) Hz) as Hval. rewrite Hval. solve_abs.
  - pose proof (limit_poly_lead_coeff l Hnz) as [f [Hf Hlim]].
    specialize (Hlim 1 ltac:(lra)) as [δ [Hδ Hfbd]].
    exists (|lead_coeff l| + 1), δ. split; [lra |].
    intros x Hx. specialize (Hfbd x Hx).
    rewrite <- Hf; try solve_abs.
Qed.

Lemma limit_pow_poly : forall k l,
  (degree l < k)%nat ->
  ⟦ lim 0 ⟧ (fun x => x ^ k * polynomial l (1/x)) = 0.
Proof.
  intros k l H.
  replace (fun x => x ^ k * polynomial l (1/x))
    with (fun x => (x ^ (k - degree l)) * (x ^ (degree l) * polynomial l (1/x))).
  2 : {
    extensionality x.
    destruct (Req_EM_T x 0) as [H1 | H1].
    - subst x. rewrite pow_ne_zero; try lia. replace (0 * _) with 0 by lra.
      rewrite pow_ne_zero; try lia. replace (0 * _) with 0 by lra. reflexivity.
    - rewrite <- Rmult_assoc. f_equal. rewrite <- pow_add. f_equal. lia.
  }
  apply limit_eq_zero_mult.
  - apply limit_0_pow. lia.
  - apply bounded_poly_1_x.
Qed.

Lemma limit_0_add : forall f1 f2 c1 c2,
  ⟦ lim 0 ⟧ f1 = c1 -> ⟦ lim 0 ⟧ f2 = c2 -> ⟦ lim 0 ⟧ (fun x => f1 x + f2 x) = c1 + c2.
Proof.
  intros. apply limit_plus; auto.
Qed.

Lemma limit_0_sub : forall f1 f2 c1 c2,
  ⟦ lim 0 ⟧ f1 = c1 -> ⟦ lim 0 ⟧ f2 = c2 -> ⟦ lim 0 ⟧ (fun x => f1 x - f2 x) = c1 - c2.
Proof.
  intros. apply limit_minus; auto.
Qed.

Lemma horizontal_split_degree_helper : forall P A B U V,
  (0 < degree A)%nat ->
  (0 < degree B)%nat ->
  (degree P < degree A + degree B)%nat ->
  (degree V < degree A)%nat ->
  (forall x, polynomial P x = polynomial U x * polynomial A x + polynomial V x * polynomial B x) ->
  (degree U < degree B)%nat.
Proof.
  intros P A B U V H_A_pos H_B_pos H_P_deg H_V_deg H_eq.
  destruct (is_zero_poly_dec U) as [H_U_zero | H_U_nZ].
  - apply zero_poly_degree_0_val in H_U_zero. rewrite H_U_zero. exact H_B_pos.
  - pose proof (limit_poly_lead_coeff U H_U_nZ) as [fU [HfU HdU]].
    destruct (is_zero_poly_dec A) as [H_A_zero | H_A_nZ].
    + apply zero_poly_degree_0_val in H_A_zero. lia.
    + pose proof (limit_poly_lead_coeff A H_A_nZ) as [fA [HfA HdA]].
      destruct (le_lt_dec (degree B) (degree U)) as [HdB_le_dU | H_U_deg_B_lt].
      2 : { exact H_U_deg_B_lt. }
      exfalso.
      
      set (k := (degree U + degree A)%nat).
      assert (Hk_gt_P : (degree P < k)%nat) by lia.
      assert (Hk_gt_V_B : (degree V + degree B < k)%nat) by lia.
      
      assert (H_P_lim : ⟦ lim 0 ⟧ (fun x : R => x ^ k * polynomial P (1 / x)) = 0).
      { apply limit_pow_poly. exact Hk_gt_P. }
      
      assert (H_VB_lim : ⟦ lim 0 ⟧ (fun x : R => x ^ k * (polynomial V (1 / x) * polynomial B (1 / x))) = 0).
      { 
        replace (fun x : R => x ^ k * (polynomial V (1 / x) * polynomial B (1 / x)))
          with (fun x : R => (x ^ (k - degree B) * polynomial V (1 / x)) * (x ^ degree B * polynomial B (1 / x))).
        2 : {
          extensionality x.
          destruct (Req_EM_T x 0) as [H1 | H1].
          - subst x. rewrite pow_ne_zero; try lia. lra.
          - rewrite <- Rmult_assoc. f_equal. rewrite Rmult_assoc. rewrite <- Rmult_assoc.
            f_equal. rewrite <- pow_add. f_equal. lia.
        }
        apply limit_eq_zero_mult.
        - apply limit_pow_poly. lia.
        - apply bounded_poly_1_x.
      }
      
      assert (H_eq2 : forall x : R, x <> 0 ->
        x ^ k * polynomial U (1/x) * polynomial A (1/x) =
        x ^ k * polynomial P (1/x) - x ^ k * (polynomial V (1/x) * polynomial B (1/x))).
      { intros x Hx. pose proof (H_eq (1/x)) as H2. lra. }
      
      assert (H_UA_lim : ⟦ lim 0 ⟧ (fun x : R => x ^ k * polynomial U (1/x) * polynomial A (1/x)) = 0).
      {
        apply limit_eq with (f1 := fun x : R => x ^ k * polynomial P (1/x) - x ^ k * (polynomial V (1/x) * polynomial B (1/x))).
        - exists 1. split; [lra |]. intros x Hx. symmetry. apply H_eq2. solve_abs.
        - replace 0 with (0 - 0) by lra. apply limit_0_sub. exact H_P_lim. exact H_VB_lim.
      }
      
      assert (H_UA_lim2 : ⟦ lim 0 ⟧ (fun x : R => fU x * fA x) = lead_coeff U * lead_coeff A).
      { apply limit_mult; auto. }
      
      assert (H_UA_lim3 : ⟦ lim 0 ⟧ (fun x : R => fU x * fA x) = 0).
      {
        apply limit_eq with (f1 := fun x : R => x ^ k * polynomial U (1/x) * polynomial A (1/x)).
        - exists 1. split; [lra |]. intros x Hx.
          rewrite HfU; try solve_abs; rewrite HfA; try solve_abs.
          unfold k. rewrite pow_add. lra.
        - exact H_UA_lim.
      }
      
      pose proof (limit_unique _ 0 _ _ H_UA_lim2 H_UA_lim3) as H_prod_0.
      apply Rmult_integral in H_prod_0.
      destruct H_prod_0 as [H_zero | H_zero].
      * apply lead_coeff_zero_iff in H_zero. contradiction.
      * apply lead_coeff_zero_iff in H_zero. contradiction.
Qed.
