From Lib Require Import Imports Notations Reals_util Sets Limit Continuity Derivative Integral Trigonometry.
Import IntervalNotations SetNotations Function_Notations DerivativeNotations LimitNotations.

Inductive expr :=
| EVar
| EConst (c : R)
| EAdd (e1 e2 : expr)
| ESub (e1 e2 : expr)
| EMul (e1 e2 : expr)
| EDiv (e1 e2 : expr)
| ENeg (e : expr)
| ESin (e : expr)
| ECos (e : expr)
| ESqrt (e : expr)
| EPow (e : expr) (n : nat)
| EApp (f : R -> R) (df : option (R -> R)) (e : expr).

Fixpoint eval (e : expr) (x : R) : R :=
  match e with
  | EVar => x
  | EConst c => c
  | EAdd e1 e2 => eval e1 x + eval e2 x
  | ESub e1 e2 => eval e1 x - eval e2 x
  | EMul e1 e2 => eval e1 x * eval e2 x
  | EDiv e1 e2 => eval e1 x / eval e2 x
  | ENeg e => - (eval e x)
  | ESin e => sin (eval e x)
  | ECos e => cos (eval e x)
  | ESqrt e => sqrt (eval e x)
  | EPow e n => (eval e x) ^ n
  | EApp f _ e => f (eval e x)
  end.

Fixpoint wf_limit_right (e : expr) (a : R) : Prop :=
  match e with
  | EVar | EConst _ => True
  | EAdd e1 e2 | ESub e1 e2 | EMul e1 e2 => wf_limit_right e1 a /\ wf_limit_right e2 a
  | EDiv e1 e2 => wf_limit_right e1 a /\ wf_limit_right e2 a /\ eval e2 a <> 0
  | ENeg e | ESin e | ECos e | EPow e _ => wf_limit_right e a
  | ESqrt e => wf_limit_right e a /\ eval e a >= 0
  | EApp f df e => wf_limit_right e a /\ ⟦ lim (eval e a) ⟧ f = f (eval e a)
  end.

Fixpoint wf_limit_left (e : expr) (a : R) : Prop :=
  match e with
  | EVar | EConst _ => True
  | EAdd e1 e2 | ESub e1 e2 | EMul e1 e2 => wf_limit_left e1 a /\ wf_limit_left e2 a
  | EDiv e1 e2 => wf_limit_left e1 a /\ wf_limit_left e2 a /\ eval e2 a <> 0
  | ENeg e | ESin e | ECos e | EPow e _ => wf_limit_left e a
  | ESqrt e => wf_limit_left e a /\ eval e a > 0
  | EApp f df e => wf_limit_left e a /\ continuous_at f (eval e a)
  end.

Definition wf_limit (e : expr) (a : R) : Prop := wf_limit_left e a /\ wf_limit_right e a.

Fixpoint wf_derive (e : expr) (x : R) : Prop :=
  match e with
  | EVar | EConst _ => True
  | EAdd e1 e2 | ESub e1 e2 | EMul e1 e2 => wf_derive e1 x /\ wf_derive e2 x
  | EDiv e1 e2 => wf_derive e1 x /\ wf_derive e2 x /\ eval e2 x <> 0
  | ENeg e | ESin e | ECos e | EPow e _ => wf_derive e x
  | ESqrt e => wf_derive e x /\ eval e x > 0
  | EApp f (Some f') e => wf_derive e x /\ ⟦ der (eval e x) ⟧ f = f'
  | EApp f None e => False
  end.

Fixpoint derive (e : expr) : expr :=
  match e with
  | EVar => EConst 1
  | EConst _ => EConst 0
  | EAdd e1 e2 => EAdd (derive e1) (derive e2)
  | ESub e1 e2 => ESub (derive e1) (derive e2)
  | EMul e1 e2 => EAdd (EMul (derive e1) e2) (EMul e1 (derive e2))
  | EDiv e1 e2 => EDiv (ESub (EMul (derive e1) e2) (EMul e1 (derive e2))) (EPow e2 2)
  | ENeg e => ENeg (derive e)
  | ESin e => EMul (ECos e) (derive e)
  | ECos e => EMul (ENeg (ESin e)) (derive e)
  | ESqrt e => EDiv (derive e) (EMul (EConst 2) (ESqrt e))
  | EPow e n => match n with 0 => EConst 0 | S k => EMul (EMul (EConst (INR n)) (EPow e k)) (derive e) end
  | EApp f (Some f') e => EMul (EApp f' (Some (λ _, 0)) e) (derive e)
  | EApp f None e => EConst 0
  end.

Lemma right_limit_eval_expr : forall e a,
  wf_limit_right e a -> ⟦ lim a⁺ ⟧ (fun x => eval e x) = eval e a.
Proof.
  induction e; intros a H; simpl in *; try solve_R; try apply right_limit_id || apply right_limit_const.
  - destruct H as [H1 H2]. apply right_limit_plus; auto.
  - destruct H as [H1 H2]. apply right_limit_minus; auto.
  - destruct H as [H1 H2]. apply right_limit_mult; auto.
  - destruct H as [H1 [H2 H3]]. apply right_limit_div; auto.
  - apply right_limit_neg; auto.
  - apply right_limit_continuous_comp; auto. apply limit_sin.
  - apply right_limit_continuous_comp; auto. apply limit_cos.
  - destruct H as [H1 H2]. apply right_limit_continuous_comp; auto. apply limit_sqrt_x.
  - apply right_limit_pow; auto.
  - destruct H as [H1 H2]. apply right_limit_continuous_comp; auto.
Qed.

Lemma left_limit_eval_expr : forall e a,
  wf_limit_left e a -> ⟦ lim a⁻ ⟧ (fun x => eval e x) = eval e a.
Proof.
  induction e; intros a H; simpl in *; try solve_R; try apply left_limit_id || apply left_limit_const.
  - destruct H as [H1 H2]. apply left_limit_plus; auto.
  - destruct H as [H1 H2]. apply left_limit_minus; auto.
  - destruct H as [H1 H2]. apply left_limit_mult; auto.
  - destruct H as [H1 [H2 H3]]. apply left_limit_div; auto.
  - apply left_limit_neg; auto.
  - apply left_limit_continuous_comp; auto. apply limit_sin.
  - apply left_limit_continuous_comp; auto. apply limit_cos.
  - destruct H as [H1 H2]. apply left_limit_continuous_comp; auto. apply limit_sqrt_x.
  - apply left_limit_pow; auto.
  - destruct H as [H1 H2]. apply left_limit_continuous_comp; auto.
Qed.

Lemma limit_eval_expr : forall e a,
  wf_limit e a -> ⟦ lim a ⟧ (fun x => eval e x) = eval e a.
Proof.
  intros e a [HL HR]. apply left_right_iff; split.
  - apply left_limit_eval_expr; auto.
  - apply right_limit_eval_expr; auto.
Qed.

Lemma continuity_correct : forall e x,
  wf_limit e x -> continuous_at (λ t, eval e t) x.
Proof.
  intros e x H. apply limit_eval_expr in H. exact H.
Qed.

Lemma derive_correct : forall e x,
  wf_derive e x -> ⟦ der x ⟧ (λ t, eval e t) = (λ t, eval (derive e) t).
Proof.
  induction e; simpl; try lra.
  - intros x _. apply theorem_10_2.
  - intros x _. apply theorem_10_1.
  - intros x [H1 H2]; apply theorem_10_3_a; auto.
  - intros x [H1 H2]. apply theorem_10_3_c; auto.
  - intros x [H1 H2]. apply theorem_10_4_a; auto.
  - intros x [H1 [H2 H3]]. pose proof theorem_10_8 as H4.
    apply derivative_at_eq_f' with (f1' := ((eval e2 ∙ eval (derive e1) - eval e1 ∙ eval (derive e2))%f / (eval e2 ∙ eval e2))%f).
    { intros y. rewrite Rmult_1_r. rewrite Rmult_comm. reflexivity. } apply H4; auto.
  - intros x H1. apply der_neg; auto.
  - intros x H1. admit.
  - intros x H1. admit.
  - intros x [H1 H2]. admit.
  - intros x H1. admit.
  - intros x. destruct df.
    -- intros [H1 H2]. apply theorem_10_9; auto.
    -- tauto.
Admitted.

Lemma derive_correct_global : forall e,
  (forall x, wf_derive e x) -> ⟦ der ⟧ (fun x => eval e x) = (fun x => eval (derive e) x).
Proof.
  intros e H1 x. apply derive_correct; auto.
Qed.

Ltac reify_constant c :=
  lazymatch type of c with
  | R => constr:(EConst c)
  | Z => let r := constr:(IZR c) in constr:(EConst r)
  | nat => let r := constr:(IZR (Z.of_nat c)) in constr:(EConst r)
  | positive => let z := constr:(Zpos c) in let r := constr:(IZR z) in constr:(EConst r)
  | _ => fail "reify_constant: Cannot parse term:" c
  end.

Ltac reify_expr x t :=
  lazymatch t with
  | x => constr:(EVar)
  | context[x] =>
      lazymatch t with
      | ?u + ?v => let e1 := reify_expr x u in let e2 := reify_expr x v in constr:(EAdd e1 e2)
      | ?u - ?v => let e1 := reify_expr x u in let e2 := reify_expr x v in constr:(ESub e1 e2)
      | ?u * ?v => let e1 := reify_expr x u in let e2 := reify_expr x v in constr:(EMul e1 e2)
      | ?u / ?v => let e1 := reify_expr x u in let e2 := reify_expr x v in constr:(EDiv e1 e2)
      | - ?u    => let e := reify_expr x u in constr:(ENeg e)
      | sin ?u  => let e := reify_expr x u in constr:(ESin e)
      | cos ?u  => let e := reify_expr x u in constr:(ECos e)
      | sqrt ?u => let e := reify_expr x u in constr:(ESqrt e)
      | ?u ^ ?n => let e := reify_expr x u in constr:(EPow e n)
      | ?h ?u =>
          lazymatch type of h with
          | R -> R =>
              let e1 := reify_expr x u in 
              let df := match goal with | [ H : ⟦ der ⟧ h = ?g |- _ ] => constr:(Some g) | _ => constr:(@None (R -> R)) end in
              constr:(EApp h df e1)
          | _ => reify_constant t
          end
      end
  | _ => reify_constant t
  end.

Ltac change_fun_to_expr :=
  let reify_current f :=
    let x := fresh "x" in intros x _;
    let fx := eval cbv beta in (f x) in
    let e := reify_expr x fx in
    instantiate (1 := fun y => eval e y); reflexivity
  in
  lazymatch goal with
  | |- ⟦ lim ?a ⟧ ?f = ?L => eapply limit_to_a_equiv; [ reify_current f | ]
  | |- ⟦ lim ?a⁺ ⟧ ?f = ?L => eapply right_limit_to_a_equiv; [ reify_current f | ]
  | |- ⟦ lim ?a⁻ ⟧ ?f = ?L => eapply left_limit_to_a_equiv; [ reify_current f | ]
  end.

Ltac change_deriv_to_eval :=
  match goal with
  | [ |- ⟦ der ⟧ _ = _ ] => eapply derivative_replace_eq
  | [ |- ⟦ der ⟧ _ _ = _ ] => apply derivative_imp_derivative_on; [ solve_R | ]
  | [ |- ⟦ der _ ⟧ _ = _ ] => eapply derivative_at_replace_eq
  end;
  [ let x := fresh "x" in intros x;
    match goal with 
    | [ |- _ = ?rhs ] =>
      let rhs_unfolded := eval unfold compose in rhs in
      let fx := eval cbv beta in rhs_unfolded in
      let e := reify_expr x fx in
      instantiate (1 := fun t => eval e t); simpl; reflexivity
    end
  | idtac ].

Ltac auto_limit :=
  intros;
  try solve [ solve_R ];
  change_fun_to_expr;
  match goal with
  | [ |- ⟦ lim ?a ⟧ (fun x => eval ?e x) = ?L ] => replace L with (eval e a) by (try (simpl; lra); solve_R); apply limit_eval_expr; repeat split; solve_R
  | [ |- ⟦ lim ?a⁺ ⟧ (fun x => eval ?e x) = ?L ] => replace L with (eval e a) by (try (simpl; lra); solve_R); apply right_limit_eval_expr; repeat split; solve_R
  | [ |- ⟦ lim ?a⁻ ⟧ (fun x => eval ?e x) = ?L ] => replace L with (eval e a) by (try (simpl; lra); solve_R); apply left_limit_eval_expr; repeat split; solve_R
  end.

Ltac auto_cont :=
  intros;
  try solve [ solve_R ];
  match goal with | [ |- continuous_on ?f ?I ] => apply continuous_imp_continuous_on | _ => idtac end;
  unfold continuous, continuous_at in *; auto_limit.

Ltac auto_diff :=
  intros;
  try solve [ solve_R ];
  try (match goal with | [ |- ⟦ der ⟧ _ _ = _ ] => apply derivative_imp_derivative_on; [ solve_R | ] end);
  change_deriv_to_eval;
  match goal with
  | [ |- ⟦ der ⟧ (fun t => eval ?e t) = ?rhs ] =>
    replace rhs with (fun t => eval (derive e) t) by (let x := fresh "x" in extensionality x; unfold compose in *; try (simpl; lra); solve_R);
    apply derive_correct_global; repeat split; solve_R
  | [ |- ⟦ der _ ⟧ (fun t => eval ?e t) = ?rhs ] =>
    replace rhs with (fun t => eval (derive e) t) by (let x := fresh "x" in extensionality x; unfold compose in *; try (simpl; lra); solve_R);
    apply derive_correct; repeat split; solve_R
  end.

Example FTC2_test : ∫ 0 1 (λ x : ℝ, 2 * x) = 1.
Proof.
  set (f := λ x : ℝ, 2 * x).
  set (g := λ x : ℝ, x^2).
  assert (H1 : 0 < 1) by lra.
  assert (H2 : continuous_on f [0, 1]) by (unfold f; auto_cont).
  assert (H3 : ⟦ der ⟧ g [0, 1] = f) by (unfold f, g; auto_diff).
  replace 1 with (g 1 - g 0) at 2 by (unfold g; lra).
  apply (FTC2 0 1 f g H1 H2 H3).
Qed.
