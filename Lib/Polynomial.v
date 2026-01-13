From Lib Require Import Imports Reals_util Sums Continuity Limit Notations.
Import LimitNotations.

Open Scope R_scope.

Local Notation length := List.length.

Definition polynomial (l : list R) : R -> R :=
  fun x => sum_f 0 (length l - 1) (fun i => nth i l 0 * x^(length l - 1 - i)).

Definition leading_coefficient (l : list R) : R := nth 0 l 0.

Fixpoint degree (l : list R) : nat :=
  match l with
  | [] => 0
  | h :: t => if Req_EM_T h 0 then degree t else length l - 1
  end.

Lemma poly_nil : forall x, polynomial ([] : list R) x = 0.
Proof.
  intro; compute. rewrite Rmult_1_r. reflexivity.
Qed.

Lemma poly_cons : forall h t x, polynomial (h :: t) x = h * x^(length t) + polynomial t x.
Proof.
  intros h t x. unfold polynomial. assert (length t = 0 \/ length t > 0)%nat as [H1 | H1] by lia.
  - rewrite length_zero_iff_nil in H1. subst; simpl; repeat rewrite sum_f_0_0; lra.
  - replace (length (h :: t) - 1)%nat with (length t) by (simpl; lia). rewrite sum_f_nth_cons_8; try lia.
    replace (x ^ (length t - 0) * h) with (h * x ^ (length t)). 2 : { rewrite Nat.sub_0_r; lra. }
    apply Rplus_eq_compat_l. apply sum_f_equiv; try lia. intros k H2.
    replace (length t - (k + 1))%nat with (length t - 1 - k)%nat by lia. reflexivity.
Qed.

Lemma continuous_at_polynomial : forall l a,
  continuous_at (polynomial l) a.
Proof.
  intros l a. induction l as [| h t IH].
  - replace (polynomial []) with (fun _ : ℝ => 0).
    2 : { extensionality x. rewrite poly_nil. reflexivity. }
    apply continuous_at_const.
  - replace (polynomial (h :: t)) with (fun x : ℝ => h * x^(length t) + polynomial t x).
    2 : { extensionality x. rewrite poly_cons. reflexivity. }
    apply continuous_at_plus; auto.
    apply continuous_at_mult.
    * apply continuous_at_const.
    * apply continuous_at_pow.
Qed.

Theorem continuous_polynomial : forall l,
  continuous (polynomial l).
Proof.
  intros l a. apply continuous_at_polynomial.
Qed.

Lemma continuous_on_polynomial : forall l D,
  continuous_on (polynomial l) D.
Proof.
  intros l D a H1. induction l as [| h t IH].
  - replace (polynomial []) with (fun _ : ℝ => 0).
    2 : { extensionality x. rewrite poly_nil. reflexivity. }
    apply limit_on_const.
  - replace (polynomial (h :: t)) with (fun x : ℝ => h * x^(length t) + polynomial t x).
    2 : { extensionality x. rewrite poly_cons. reflexivity. }
    apply limit_on_plus.
    + apply limit_on_mult.
      * apply limit_on_const.
      * apply limit_on_pow. apply limit_on_id.
    + apply IH. 
Qed.

Lemma poly_shift : forall l c x,
  polynomial (l ++ [c]) x = x * polynomial l x + c.
Proof.
  intros.
  destruct l as [|a l].
  - simpl. unfold polynomial. simpl. repeat rewrite sum_f_0_0. lra.
  - unfold polynomial.
    rewrite length_app. 
    replace (length (a :: l) + length [c] - 1)%nat with (S (length l)) by (simpl; lia).
    replace (length (a :: l)) with (S (length l)) by (simpl; lia).
    rewrite sum_f_i_Sn_f; try lia.
    rewrite Rplus_comm.
    rewrite (Rplus_comm (x * _)).
    f_equal.
    + rewrite app_nth2. 2 : { simpl; lia. }
      rewrite Nat.sub_diag. simpl. rewrite Nat.sub_diag. lra.
    + rewrite r_mult_sum_f_i_n_f_l.
      replace (S (length l) - 1)%nat with (length l) by lia.
      apply sum_f_equiv; try lia.
      intros k H2.
      rewrite app_nth1. 2 : { simpl; lia. }
      replace (S (length l) - k)%nat with (S (length l - k))%nat by lia.
      simpl. lra.
Qed.

Lemma limit_poly_offset : forall l a,
  ⟦ lim a ⟧ (fun x => polynomial l (x - a)) = polynomial l 0.
Proof.
  intros l a.
  destruct l as [|c l] using rev_ind.
  - simpl. replace (λ x : ℝ, polynomial [] (x - a)) with (λ x : ℝ, 0).
    2 : { extensionality x. rewrite poly_nil. reflexivity. }
    rewrite poly_nil. apply limit_const.
  - rewrite !poly_shift.
    apply limit_eq with (f1 := fun x => (x - a) * polynomial l (x - a) + c).
    + exists 1. split; try lra. intros x H1. rewrite poly_shift. reflexivity.
    + apply limit_plus_const. apply limit_mult; auto.
      replace 0 with (a - a) by lra. apply limit_minus; [apply limit_id | apply limit_const].
Qed.

Lemma poly_decompose : forall l, exists t c, 
  (forall x, polynomial l x = x * polynomial t x + c) /\
  (length t = pred (length l)).
Proof.
  intros l. induction l as [| c l' _] using rev_ind.
  - exists [], 0. split.
    + intros x. rewrite poly_nil. lra.
    + simpl. reflexivity.
  - exists l', c. split.
    + intros x. rewrite poly_shift. reflexivity.
    + rewrite length_app. simpl. lia.
Qed.