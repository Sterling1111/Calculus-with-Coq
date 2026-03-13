Require Import Imports PolySimp.

Open Scope Z_scope.

Definition Formulae := list Expr.

Fixpoint eval_form (env : Env) (f : Formulae) : Prop :=
  match f with
  | [] => False
  | e :: ft => ((eval_expr env e) >= 0) -> (eval_form env ft)
  end.

Inductive Cone (f : Formulae) : Ensemble Expr :=
| IsGen    : forall p, In p f -> Cone f p
| IsSquare : forall p, Cone f (Mult p p)
| IsMult   : forall p q, Cone f p -> Cone f q -> Cone f (Mult p q)
| IsAdd    : forall p q, Cone f p -> Cone f q -> Cone f (Add p q)
| IsPos    : forall c, (c >= 0)%Z -> Cone f (Const c).

Lemma cone_pos : forall (f : Formulae) (e : Expr) (env : Env),
  Cone f e ->
  (forall p, In p f -> eval_expr env p >= 0) ->
  eval_expr env e >= 0.
Proof.
  intros f e env H1 H2.
  induction H1 as [p H1 | p | p q H1 IH1 H3 IH2 | p q H1 IH1 H3 IH2 | c H1]; auto.
  - simpl. apply sqr_pos.
  - simpl. apply Z.le_ge. apply Z.ge_le in IH1, IH2. apply Z.mul_nonneg_nonneg; auto.
  - simpl. apply Z.le_ge. apply Z.ge_le in IH1, IH2. apply Z.add_nonneg_nonneg; auto.
Qed.

Lemma list_to_eval : forall env (f : Formulae),
  ((forall p, In p f -> eval_expr env p >= 0) -> False) ->
  eval_form env f.
Proof.
  intros env f H1.
  induction f as [| a f' IH]; simpl in *.
  - apply H1. intros p H2. exfalso; auto.
  - intros H2. apply IH. intros H3.
    apply H1. intros p [H4 | H4]; subst; auto.
Qed.

Theorem positivstellensatz : forall f env,
  (exists e, Cone f e /\ forall env', eval_expr env' e = -1) ->
  eval_form env f.
Proof.
  intros f env [e [H1 H2]].
  apply list_to_eval; intros H3.
  apply cone_pos with (env := env) in H1; auto.
  rewrite H2 in H1.
  compute in H1. apply H1. reflexivity.
Qed.

Inductive Certificate : Set :=
  | Cert_isGen (n : nat)
  | Cert_isSquare (e : Expr)
  | Cert_isMult (c1 c2 : Certificate)
  | Cert_isAdd (c1 c2 : Certificate)
  | Cert_isZpos (p : positive)
  | Cert_IsZ0.

Fixpoint decode (f : Formulae) (c : Certificate) : Expr :=
  match c with
  | Cert_isGen n => nth n f (Const 0)
  | Cert_isSquare p => Mult p p
  | Cert_isMult p q => Mult (decode f p) (decode f q)
  | Cert_isAdd p q => Add (decode f p) (decode f q)
  | Cert_isZpos p => Const (Z.pos p)
  | Cert_IsZ0 => Const 0
  end.

Definition checker (c : Certificate) (f : list Expr) : bool :=
  (polynomial_simplify (decode f c)) == -1.

Lemma cert_in_cone : forall f c, Cone f (decode f c).
Proof.
  intros f c.
  induction c as [n | e | c1 H1 c2 H2 | c1 H1 c2 H2 | p | ]; simpl.
  - destruct (lt_dec n (length f)) as [H1 | H1].
    + apply IsGen, nth_In, H1.
    + rewrite nth_overflow.
      * apply IsPos. compute. intros H2. discriminate H2.
      * apply Nat.nlt_ge, H1.
  - apply IsSquare.
  - apply IsMult; assumption.
  - apply IsAdd; assumption.
  - apply IsPos, Z.le_ge, Zle_0_pos.
  - apply IsPos. compute. intros H1. discriminate H1.
Qed.

Lemma checker_correct_value :
  forall f c,
    checker c f = true ->
    forall env', eval_expr env' (decode f c) = -1.
Proof.
  intros f c H env'.
  unfold checker in H.
  apply expr_eqb_correct with (env := env') in H.
  rewrite <- polynomial_simplify_correct.
  exact H.
Qed.

Theorem checker_sound : forall f c env,
  checker c f = true ->
  eval_form env f.
Proof.
  intros f c env H1.
  apply positivstellensatz.
  exists (decode f c).
  split; [apply cert_in_cone | apply checker_correct_value; auto ].
Qed.

Declare ML Module "simplex_plugin.plugin".

Lemma eq_to_ge : forall a b : Z, a = b -> a - b >= 0 /\ b - a >= 0.
Proof.
  intros a b H1.
  lia.
Qed.

Lemma ge_to_ge0 : forall a b : Z, a >= b -> a - b >= 0.
Proof.
  intros a b H1.
  lia.
Qed.

Lemma gt_to_ge0 : forall a b : Z, a > b -> a - b - 1 >= 0.
Proof.
  intros a b H1.
  lia.
Qed.

Lemma le_to_ge0 : forall a b : Z, a <= b -> b - a >= 0.
Proof.
  intros a b H1.
  lia.
Qed.

Lemma lt_to_ge0 : forall a b : Z, a < b -> b - a - 1 >= 0.
Proof.
  intros a b H1.
  lia.
Qed.

Lemma prove_Zge : forall a b : Z, (b - a - 1 >= 0 -> False) -> a >= b.
Proof.
  intros a b H1.
  lia.
Qed.

Lemma prove_Zle : forall a b : Z, (a - b - 1 >= 0 -> False) -> a <= b.
Proof.
  intros a b H1.
  lia.
Qed.

Lemma prove_Zgt : forall a b : Z, (b - a >= 0 -> False) -> a > b.
Proof.
  intros a b H1.
  lia.
Qed.

Lemma prove_Zlt : forall a b : Z, (a - b >= 0 -> False) -> a < b.
Proof.
  intros a b H1.
  lia.
Qed.

Lemma prove_Zeq : forall a b : Z, (a - b - 1 >= 0 -> False) -> (b - a - 1 >= 0 -> False) -> a = b.
Proof.
  intros a b H1 H2.
  lia.
Qed.

Ltac negate_goal :=
  intros;
  match goal with
  | |- (?A >= ?B)%Z => apply prove_Zge; intro
  | |- (?A <= ?B)%Z => apply prove_Zle; intro
  | |- (?A > ?B)%Z => apply prove_Zgt; intro
  | |- (?A < ?B)%Z => apply prove_Zlt; intro
  | |- @eq Z ?A ?B => apply prove_Zeq; intro
  | |- False => idtac
  end.

Ltac is_not_Z0 e :=
  match e with
  | Z0 => constr:(false)
  | 0%Z => constr:(false)
  | _ => constr:(true)
  end.

Ltac normalize_hyps :=
  repeat match goal with
  | H1 : @eq Z ?A ?B |- _ =>
      let H2 := fresh "H" in apply eq_to_ge in H1; destruct H1 as [H1 H2]
  | H1 : (?A > ?B)%Z |- _ => apply gt_to_ge0 in H1
  | H1 : (?A <= ?B)%Z |- _ => apply le_to_ge0 in H1
  | H1 : (?A < ?B)%Z |- _ => apply lt_to_ge0 in H1
  | H1 : (?A >= ?B)%Z |- _ =>
      let b := is_not_Z0 B in
      match b with
      | true => apply ge_to_ge0 in H1
      end
  end.

Ltac find_var x vars :=
  match vars with
  | x :: _ => constr:(1%positive)
  | _ :: ?rest => 
      let p := find_var x rest in 
      constr:(Pos.succ p)
  | nil => constr:(1%positive)
  end.

Ltac get_vars e acc :=
  match e with
  | (?A + ?B)%Z => let acc1 := get_vars A acc in get_vars B acc1
  | (?A - ?B)%Z => let acc1 := get_vars A acc in get_vars B acc1
  | (?A * ?B)%Z => let acc1 := get_vars A acc in get_vars B acc1
  | (- ?A)%Z => get_vars A acc
  | Z0 => acc
  | Zpos _ => acc
  | Zneg _ => acc
  | ?C => match acc with context [C] => acc | _ => constr:(C :: acc) end
  end.

Ltac get_vars_from_goal G acc :=
  match G with
  | (?A >= ?B)%Z -> ?Rest =>
      let acc1 := get_vars A acc in
      get_vars_from_goal Rest acc1
  | _ => acc
  end.

Ltac reify_expr vars e :=
  match e with
  | (?A + ?B)%Z => 
      let rA := reify_expr vars A in 
      let rB := reify_expr vars B in 
      constr:(Add rA rB)
  | (?A - ?B)%Z => 
      let rA := reify_expr vars A in 
      let rB := reify_expr vars B in 
      constr:(Add rA (Neg rB))
  | (?A * ?B)%Z => 
      let rA := reify_expr vars A in 
      let rB := reify_expr vars B in 
      constr:(Mult rA rB)
  | (- ?A)%Z => 
      let rA := reify_expr vars A in 
      constr:(Neg rA)
  | Z0 => constr:(Const e)
  | Zpos _ => constr:(Const e)
  | Zneg _ => constr:(Const e)
  | ?C => let n := find_var C vars in constr:(Var n)
  end.

Ltac reify_goal vars G :=
  match G with
  | (?A >= ?B)%Z -> ?Rest =>
      let rA := reify_expr vars A in
      let f := reify_goal vars Rest in
      constr:(rA :: f)
  | _ => constr:(@nil Expr)
  end.

Ltac mk_env vars :=
  let rec aux vs p :=
    match vs with
    | ?x :: ?rest =>
        let env_rest := aux rest (Pos.succ p) in
        constr:(PMap.add p x env_rest)
    | nil => constr:(@PMap.empty Z)
    end
  in aux vars 1%positive.

Ltac revert_hyps :=
  match goal with
  | H1 : (?A >= ?B)%Z |- _ => revert H1; revert_hyps
  | |- _ => idtac
  end.

Lemma vm_cast_prop : forall P Q : Prop, P = Q -> P -> Q.
Proof.
  intros P Q H1 H2.
  rewrite <- H1.
  exact H2.
Qed.

Ltac reify_step :=
  match goal with
  | |- ?G =>
      let vars := get_vars_from_goal G (@nil Z) in
      let e := mk_env vars in
      let f' := reify_goal vars G in
      let e_cbv := eval cbv in e in
      let f_cbv := eval cbv in f' in
      pose (env := e_cbv);
      pose (f := f_cbv)
  end.

Ltac psatz_core :=
  normalize_hyps;
  revert_hyps;
  unfold Z.sub;
  match goal with
  | |- ?G =>
      let vars := get_vars_from_goal G (@nil Z) in
      let env := mk_env vars in
      let f := reify_goal vars G in
      let env_cbv := eval cbv in env in
      let f_cbv := eval cbv in f in
      
      apply vm_cast_prop with (P := eval_form env_cbv f_cbv);
      [ cbv -[Z.add Z.sub Z.mul Z.opp Z.ge Z.gt Z.le Z.lt]; reflexivity
        
      | let cert_name := fresh "cert" in
        call_simplex_plugin cert_name f_cbv;
        match goal with
        | H1 := _ |- _ => apply checker_sound with (c := H1)
        end;
        vm_compute; reflexivity ]
  end.

Tactic Notation "psatz" := negate_goal; psatz_core.

Lemma test_chain : forall x y z w : Z,
  x > y ->
  y > z ->
  z > w ->
  x >= w + 3.
Proof.
  intros.
  negate_goal.
  normalize_hyps.
  revert_hyps;
  reify_step.
  apply vm_cast_prop with (P := eval_form env f).
  cbv -[Z.add Z.sub Z.mul Z.opp Z.ge Z.gt Z.le Z.lt]; auto.
  let f_cbv := eval cbv in f in call_simplex_plugin cert f_cbv.
  apply checker_sound with (c := cert).
  vm_compute. reflexivity.
Qed.

Lemma gt_implies_succ_le :
  forall a b : Z, a > b -> b + 1 <= a.
Proof.
  intros a b H1.
  unfold Z.gt in H1.
  apply Z.lt_succ_r.
  apply Z.add_lt_mono_r.
  apply Z.compare_gt_iff.
  exact H1.
Qed.

Theorem chain_gt_three :
  forall x y z w : Z,
    x > y -> y > z -> z > w -> x >= w + 3.
Proof.
  intros x y z w H1 H2 H3.

  pose proof gt_implies_succ_le x y H1 as H4.
  pose proof gt_implies_succ_le y z H2 as H5.
  pose proof gt_implies_succ_le z w H3 as H6.

  assert (H7 : w + 2 <= y).
  {
    replace (w + 2) with (w + (1 + 1)) by reflexivity.
    rewrite Z.add_assoc.
    apply Z.le_trans with (m := z + 1).
    - apply Z.add_le_mono_r. apply H6.
    - apply H5.
  }

  assert (H8 : w + 3 <= x).
  {
    replace (w + 3) with (w + (2 + 1)) by reflexivity.
    rewrite Z.add_assoc.
    apply Z.le_trans with (m := y + 1).
    - apply Z.add_le_mono_r. apply H7.
    - apply H4.
  }

  apply Z.le_ge.
  apply H8.
Qed.

Theorem new :
  forall x y z w : Z,
    x > y -> y > z -> z > w -> x >= w + 3.
Proof.
  psatz.
Qed.

Lemma test_dense : forall a b c : Z,
  a + b >= 10 ->
  b + c >= 10 ->
  a + c >= 10 ->
  a + b + c >= 15.
Proof.
  psatz.
Qed.

Lemma test_hard : forall a b c d e f : Z,
  a + b + c + d + e + f >= 100 ->
  a - b + c - d + e - f <= 10 ->
  2 * a + 3 * b - c + 4 * d - 2 * e + f >= 50 ->
  -a + 2 * b + 2 * c - d + 3 * e + 4 * f >= 60 ->
  a + b <= 15 ->
  c + d <= 15 ->
  e + f >= 70.
Proof.
  psatz.
Qed.

Lemma massive_test_8 : forall x0 x1 x2 x3 x4 x5 x6 x7 : Z,
  x0 + x1 - x2 + x3 - x4 + x5 - x6 + x7 >= 5 ->
  -x0 + 2 * x1 + x2 - x3 + 2 * x4 - x5 + x6 - x7 >= 3 ->
  2 * x0 - x1 + 2 * x2 + 2 * x3 - x4 + 2 * x5 - x6 + x7 >= 8 ->
  -2 * x0 + x1 - 2 * x2 + x3 + 2 * x4 - x5 + 2 * x6 - x7 >= -2 ->
  x0 - 2 * x1 + x2 - 2 * x3 + x4 + 2 * x5 - x6 + 2 * x7 >= 4 ->
  2 * x0 + 2 * x1 - x2 + 2 * x3 - 2 * x4 + x5 + 2 * x6 - x7 >= 7 ->
  -x0 - x1 + 2 * x2 - x3 + 2 * x4 - 2 * x5 + x6 + 2 * x7 >= -1 ->
  x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 >= 10 ->
  -3 * x0 - 3 * x1 - 3 * x2 - 3 * x3 - 4 * x4 - 3 * x5 - 4 * x6 - 4 * x7 >= -33 ->
  False.
Proof.
  psatz.
Qed.

Lemma massive_test_10 : forall x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 : Z,
  x0 + 2 * x1 - 3 * x2 + x3 + 4 * x4 - x5 + 2 * x6 - x7 + x8 + x9 >= 5 ->
  -2 * x0 + x1 + x2 - 2 * x3 + x4 + 3 * x5 - x6 + 2 * x7 - 2 * x8 + x9 >= -3 ->
  3 * x0 - x1 + 2 * x2 + x3 - 2 * x4 + x5 + 3 * x6 - x7 + x8 - 2 * x9 >= 7 ->
  x0 + x1 - x2 + 3 * x3 + x4 - 2 * x5 + x6 + x7 + 2 * x8 + x9 >= 4 ->
  -x0 - 2 * x1 + x2 - x3 + 2 * x4 + x5 - 2 * x6 + 3 * x7 - x8 + 2 * x9 >= 1 ->
  2 * x0 + x1 + 3 * x2 + 2 * x3 - x4 - x5 + x6 - 2 * x7 + 3 * x8 - x9 >= 8 ->
  -3 * x0 + 2 * x1 - 2 * x2 + x3 + 3 * x4 + 2 * x5 - x6 + x7 - x8 + 3 * x9 >= 0 ->
  x0 - 3 * x1 + x2 + 2 * x3 - x4 + 3 * x5 + 2 * x6 - x7 + 2 * x8 + x9 >= 2 ->
  2 * x0 + x1 - x2 - 2 * x3 + x4 + x5 - 3 * x6 + 2 * x7 + x8 - x9 >= -1 ->
  x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 >= 10 ->
  -5 * x0 - 3 * x1 - 2 * x2 - 6 * x3 - 9 * x4 - 8 * x5 - 3 * x6 - 5 * x7 - 7 * x8 - 6 * x9 >= -32 ->
  False.
Proof.
  psatz.
Qed.