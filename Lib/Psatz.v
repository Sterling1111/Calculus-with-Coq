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

Fixpoint decode (P : list Expr) (c : Certificate) : Expr :=
  match c with
  | Cert_isGen n => nth n P (Const 0)
  | Cert_isSquare p => Mult p p
  | Cert_isMult p q => Mult (decode P p) (decode P q)
  | Cert_isAdd p q => Add (decode P p) (decode P q)
  | Cert_isZpos p => Const (Z.pos p)
  | Cert_IsZ0 => Const 0
  end.

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

Definition checker (c : Certificate) (P : list Expr) : bool :=
  (polynomial_simplify (decode P c)) == -1.

Theorem checker_sound : forall f c env,
  checker c f = true ->
  eval_form env f.
Proof.
  intros f c env H1.
  apply positivstellensatz.
  exists (decode f c).
  split.
  - apply cert_in_cone.
  - intros env'.
    unfold checker in H1.
    apply expr_eqb_correct with (env := env') in H1.
    rewrite <- polynomial_simplify_correct.
    exact H1.
Qed.