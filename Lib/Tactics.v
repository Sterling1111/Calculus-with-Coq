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
| EApp (f : R -> R) (f' : R -> R) (e : expr).

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

Fixpoint wf_expr (e : expr) (x : R) : Prop :=
  match e with
  | EVar | EConst _ => True
  | EAdd e1 e2 | ESub e1 e2 | EMul e1 e2 =>
      wf_expr e1 x /\ wf_expr e2 x
  | EDiv e1 e2 =>
      wf_expr e1 x /\ wf_expr e2 x /\ eval e2 x <> 0
  | ENeg e | ESin e | ECos e | EPow e _ => 
      wf_expr e x
  | ESqrt e => 
      wf_expr e x /\ eval e x > 0
  | EApp f f' e =>
      wf_expr e x /\ ⟦ der (eval e x) ⟧ f = f'
  end.

Fixpoint derive (e : expr) : expr :=
  match e with
  | EVar => EConst 1
  | EConst _ => EConst 0
  | EAdd e1 e2 => EAdd (derive e1) (derive e2)
  | ESub e1 e2 => ESub (derive e1) (derive e2)
  | EMul e1 e2 => 
      EAdd (EMul (derive e1) e2) (EMul e1 (derive e2))
  | EDiv e1 e2 => 
      EDiv (ESub (EMul (derive e1) e2) (EMul e1 (derive e2))) (EPow e2 2)
  | ENeg e => ENeg (derive e)
  | ESin e => EMul (ECos e) (derive e)
  | ECos e => EMul (ENeg (ESin e)) (derive e)
  | ESqrt e => 
      EDiv (derive e) (EMul (EConst 2) (ESqrt e))
  | EPow e n =>
      match n with
      | 0 => EConst 0
      | S k => EMul (EMul (EConst (INR n)) (EPow e k)) (derive e)
      end
  | EApp f f' e => EMul (EApp f' (λ _, 0) e) (derive e)
  end.

Lemma derive_correct : forall e x,
  wf_expr e x ->
  ⟦ der x ⟧ (λ t, eval e t) = (λ t, eval (derive e) t).
Proof.
  induction e; simpl; try lra.
  - intros x _. apply theorem_10_2.
  - intros x _. apply theorem_10_1.
  - intros x [H1 H2]; apply theorem_10_3_a; auto.
  - intros x [H1 H2]. apply theorem_10_3_c; auto.
  - intros x [H1 H2]. apply theorem_10_4_a; auto.
  - intros x [H1 [H2 H3]]. pose proof theorem_10_8 (eval e1) (eval (derive e1)) (eval e2) (eval (derive e2)) x as H4.
    apply derivative_at_eq_f' with (f1' := ((eval e2 ∙ eval (derive e1) - eval e1 ∙ eval (derive e2))%f / (eval e2 ∙ eval e2))%f).
    { intros y. rewrite Rmult_1_r. rewrite Rmult_comm. reflexivity. }
    apply H4; auto.
  - intros x H1. apply der_neg; auto.
  - intros x H1. (*chain rule here*) admit.
  - intros x H1. (*chain rule here*) admit.
  - intros x [H1 H2]. admit.
  - intros x H1. admit.
  - intros x [H1 H2]. apply theorem_10_9; auto.
Admitted.

Lemma derive_correct_global : forall e,
  (forall x, wf_expr e x) -> (* Expression must be valid everywhere *)
  ⟦ der ⟧ (fun x => eval e x) = (fun x => eval (derive e) x).
Proof.
  intros e H1 x. apply derive_correct; auto.
Qed.

Ltac reify_constant c :=
  lazymatch type of c with
  | R => constr:(EConst c)
  | Z => let r := constr:(IZR c) in constr:(EConst r)
  | nat => let z := constr:(Z.of_nat c) in let r := constr:(IZR z) in constr:(EConst r)
  | positive => let z := constr:(Zpos c) in let r := constr:(IZR z) in constr:(EConst r)
  | _ => fail "reify_expr: Cannot parse term or unsupported constant:" c
  end.

Ltac reify_expr x t :=
  lazymatch t with
  | x           => constr:(EVar)
  (* Standard Operators *)
  | ?u + ?v     => let e1 := reify_expr x u in let e2 := reify_expr x v in constr:(EAdd e1 e2)
  | ?u - ?v     => let e1 := reify_expr x u in let e2 := reify_expr x v in constr:(ESub e1 e2)
  | ?u * ?v     => let e1 := reify_expr x u in let e2 := reify_expr x v in constr:(EMul e1 e2)
  | ?u / ?v     => let e1 := reify_expr x u in let e2 := reify_expr x v in constr:(EDiv e1 e2)
  | - ?u        => let e := reify_expr x u in constr:(ENeg e)
  | sin ?u      => let e := reify_expr x u in constr:(ESin e)
  | cos ?u      => let e := reify_expr x u in constr:(ECos e)
  | sqrt ?u     => let e := reify_expr x u in constr:(ESqrt e)
  | ?u ^ ?n     => let e := reify_expr x u in constr:(EPow e n)
  
  (* Arbitrary Function App (With Type Check!) *)
  | ?f ?u =>
      let Tf := type of f in
      lazymatch Tf with
      | R -> R => 
          (* It IS a real function (e.g. f(x), g(x)) *)
          let e := reify_expr x u in
          let df := match goal with
                    | [ H : ⟦ der ⟧ f = ?g |- _ ] => constr:(g)
                    | [ H : forall t, ⟦ der t ⟧ f = ?g t |- _ ] => constr:(g)
                    | _ => fail "reify_expr: No derivative hypothesis found for function" f
                    end in
          constr:(EApp f df e)
      | _ => 
          (* It is NOT a real function (e.g. 'xI' constructor for positive numbers) *)
          reify_constant t
      end
  
  (* Atomic Constants *)
  | ?c          => reify_constant c
  end.

  Ltac change_deriv_to_eval :=
  eapply derivative_replace_eq;
  [ let x := fresh "x" in intros x;
    match goal with 
    | [ |- _ = ?rhs ] =>
      let rhs_unfolded := eval unfold compose in rhs in
      let fx := eval cbv beta in rhs_unfolded in
      let e := reify_expr x fx in
      instantiate (1 := fun t => eval e t);
      simpl; reflexivity
    end
  | idtac ].

Ltac auto_diff :=
  intros;
  change_deriv_to_eval;
  match goal with
  | [ |- ⟦ der ⟧ (fun t => eval ?e t) = ?rhs ] =>
    replace rhs with (fun t => eval (derive e) t) by (extensionality x; unfold compose in *; solve_R);
    apply derive_correct_global; repeat split; solve_R
  end.

Lemma diff_test_trig_compose : ⟦ der ⟧ (λ x, sin (x^2)) = λ x, cos(x^2) * 2*x.
Proof.
  auto_diff.
Qed.

Lemma diff_test_chain_poly : ⟦ der ⟧ (λ x, (x^2 + 1) ^ 3) = λ x, 6*x * (x^2 + 1)^2.
Proof.
  auto_diff.
Qed.

Lemma diff_test_safe_div : ⟦ der ⟧ (λ x, 1 / (x^2 + 1)) = (λ x, -2*x / (x^2 + 1)^2).
Proof.
  auto_diff.
Qed.

Lemma diff_test_boss : 
  ⟦ der ⟧ (fun x => sin (1 / (x^2 + 1))) = 
  (fun x => cos (1 / (x^2 + 1)) * (-2 * x / (x^2 + 1)^2)).
Proof.
  auto_diff.
Qed.

Lemma sin_comp_diff_test : 
  ⟦ der ⟧ (fun x => sin (cos (cos (1 + x^2)))) =
  (fun x =>
     cos (cos (cos (1 + x^2))) *
     sin (cos (1 + x^2)) *
     sin (1 + x^2) *
     (2 * x)).
Proof.
  auto_diff.
Qed.

Lemma diff_insane :
  ⟦ der ⟧
    (fun x =>
       cos (sin (cos (sin (cos (sin (x^2 + 3*x + 7)))))))
  =
  (fun x =>
     - sin (sin (cos (sin (cos (sin (x^2 + 3*x + 7)))))) *
       cos (cos (sin (cos (sin (x^2 + 3*x + 7))))) *
       sin (sin (cos (sin (x^2 + 3*x + 7)))) *
       cos (cos (sin (x^2 + 3*x + 7))) *
       sin (sin (x^2 + 3*x + 7)) *
       cos (x^2 + 3*x + 7) *
       (2*x + 3)).
Proof.
  auto_diff.
Qed.

Lemma auto_chain_test : forall f f' g g' h h' i i',
  ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> ⟦ der ⟧ h = h' -> ⟦ der ⟧ i = i' ->
  ⟦ der ⟧ (f ∘ g ∘ h ∘ i) = (f' ∘ g ∘ h ∘ i) ∙ (g' ∘ h ∘ i) ∙ (h' ∘ i) ∙ i'.
Proof.
  auto_diff.
Qed.