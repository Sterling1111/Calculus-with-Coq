From Lib Require Import Imports Limit Sets Notations Functions Reals_util Tactics.
Require Export ATTAM.Chapter35.
Import SetNotations LimitNotations.

Lemma lemma_36_1 : ⟦ lim 4 ⟧ (fun x => 2 * x + 3) = 11.
Proof.
  intros ε H1. exists (ε/2). split. apply Rdiv_pos_pos. lra. lra. intros x H2.
  solve_R.
Qed.

Lemma lemma_36_1' : ⟦ lim 4 ⟧ (fun x => x^3 + 3 * x^2 + 2 * x - 15) = 105.
Proof. solve_lim. Qed.

Lemma lemma_36_1'' : ⟦ lim 4 ⟧ (fun x => x^3 + 3 * x^2 + 2 * x - 15) = 105.
Proof.
  change_fun_to_expr;
  set (e := (ESub (EAdd (EAdd (EPow EVar 3) 
            (EMul (EConst 3) (EPow EVar 2))) (EMul (EConst 2) EVar)) (EConst 15))).
  apply limit_subst with (L1 := eval_expr e 4).
  - simpl. field_simplify. reflexivity.
  - apply limit_eval_expr. compute. tauto.
Qed.

Lemma lemma_36_1''' : ⟦ lim 4 ⟧ (fun x => x^3 + 3 * x^2 + 2 * x - 15) = 105.
Proof.
  replace 105 with (4^3 + 3 * 4^2 + 2 * 4 - 15) by field.
  apply limit_plus.
  - apply limit_plus.
    + apply limit_plus.
      * apply limit_pow. apply limit_id.
      * apply limit_mult.
        -- apply limit_const.
        -- apply limit_pow. apply limit_id.
    + apply limit_mult.
      * apply limit_const.
      * apply limit_id.
  - apply limit_const.
Qed.

Lemma lemma_36_2 : forall a c d, ⟦ lim a ⟧ (fun x => c * x + d) = c * a + d.
Proof.
  intros a c d. intros ε H1. assert (c = 0 \/ c <> 0) as [H2 | H2] by lra.
  - exists 1. split; solve_R.
  - exists (ε / Rabs c). split. apply Rdiv_pos_pos; solve_R. intros x [H3 H4].
    replace (c * x + d - (c * a + d)) with (c * (x - a)) by lra. 
    apply Rmult_lt_compat_r with (r := Rabs c) in H4; field_simplify in H4; solve_R.
Qed.

Lemma lemma_36_2' : forall a c d, ⟦ lim a ⟧ (fun x => c * x + d) = c * a + d.
Proof. intros. solve_lim. Qed.

Lemma lemma_36_3 :  ⟦ lim 5 ⟧ (fun x => x^2 + 3 * x + 3) = 43.
Proof.
  intros ε H1. exists (Rmin 1 (ε/14)). split. solve_R. intros x H2.
  replace (x^2 + 3 * x + 3 - 43) with ((x - 5) * (x + 8)) by lra.
  solve_R.
Qed.

Lemma lemma_36_3' : ⟦ lim 5 ⟧ (fun x => x^2 + 3 * x + 3) = 43.
Proof. solve_lim. Qed.

Lemma lemma_36_4 : ⟦ lim 2 ⟧ (fun x => (7 * x + 4) / (4 * x + 1)) = 2.
Proof. solve_lim. Qed.

Lemma lemma_36_5 : ⟦ lim 3 ⟧ (fun x => x^3 + x^2 + 2) = 38.
Proof.
  intros ε H1. exists (Rmin 1 (ε/44)). split. solve_R. intros x [H2 H3].
  replace (x^3 + x^2 + 2 - 38) with ((x - 3) * (x^2 + 4 * x + 12)) by lra.
  
  solve_R.
Admitted.

Lemma lemma_36_5' : ⟦ lim 3 ⟧ (fun x => x^3 + x^2 + 2) = 38.
Proof. solve_lim. Qed.