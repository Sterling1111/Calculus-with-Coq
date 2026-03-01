Require Import Imports.

Module PMap := PositiveMap.

Definition Env := PMap.t Z.

Inductive Expr :=
  | Var (v : positive)
  | Const (c : Z)
  | Mult (e1 e2 : Expr)
  | Add (e1 e2 : Expr)
  | Neg (e : Expr).

Definition get_env (env : Env) (v : positive) : Z :=
  match PMap.find v env with
  | Some val => val
  | None => 0%Z
  end.

Fixpoint eval_expr (env : Env) (exp : Expr) : Z :=
  match exp with 
  | Var v => get_env env v
  | Const c => c
  | Mult e1 e2 => (eval_expr env e1) * (eval_expr env e2)
  | Add e1 e2 => (eval_expr env e1) + (eval_expr env e2)
  | Neg e => - (eval_expr env e)
  end.

Definition make_env (l : list (positive * Z)) : Env :=
  fold_right (fun p env => PMap.add (fst p) (snd p) env) (PMap.empty Z) l.

Open Scope positive_scope.
Open Scope Z_scope.

Fixpoint merge_vars (l1 : list positive) : list positive -> list positive :=
  match l1 with
  | [] => fun l2 => l2
  | x :: xs =>
      fix merge_vars_inner (l2 : list positive) : list positive :=
        match l2 with
        | [] => l1
        | y :: ys =>
            match Pos.compare x y with
            | Lt => x :: merge_vars xs l2
            | _ => y :: merge_vars_inner ys
            end
        end
  end.

Fixpoint var_list_compare (l1 l2 : list positive) : comparison :=
  match l1, l2 with
  | [], [] => Eq
  | [], _ => Lt
  | _, [] => Gt
  | x::xs, y::ys =>
      match Pos.compare x y with
      | Eq => var_list_compare xs ys
      | c => c
      end
  end.

Definition Poly := list (list positive * Z)%type.

Fixpoint add_poly (p1 : Poly) : Poly -> Poly :=
  match p1 with
  | [] => fun p2 => p2
  | (v1, c1) :: ps1 =>
      fix add_poly_inner (p2 : Poly) : Poly :=
        match p2 with
        | [] => p1
        | (v2, c2) :: ps2 =>
            match var_list_compare v1 v2 with
            | Eq =>
                let c := (c1 + c2)%Z in
                if Z.eqb c 0%Z then add_poly ps1 ps2
                else (v1, c) :: add_poly ps1 ps2
            | Lt => (v1, c1) :: add_poly ps1 p2
            | Gt => (v2, c2) :: add_poly_inner ps2
            end
        end
  end.

Fixpoint mul_term_poly (v1 : list positive) (c1 : Z) (p : Poly) : Poly :=
  match p with
  | [] => []
  | (v2, c2) :: ps =>
      let c := (c1 * c2)%Z in
      if Z.eqb c 0%Z then mul_term_poly v1 c1 ps
      else add_poly [(merge_vars v1 v2, c)] (mul_term_poly v1 c1 ps)
  end.

Fixpoint mul_poly (p1 p2 : Poly) : Poly :=
  match p1 with
  | [] => []
  | (v, c) :: ps => add_poly (mul_term_poly v c p2) (mul_poly ps p2)
  end.

Fixpoint expr_to_poly (e : Expr) : Poly :=
  match e with
  | Var v => [([v], 1%Z)]
  | Const c => if Z.eqb c 0%Z then [] else [([], c)]
  | Mult e1 e2 => mul_poly (expr_to_poly e1) (expr_to_poly e2)
  | Add e1 e2 => add_poly (expr_to_poly e1) (expr_to_poly e2)
  | Neg e1 => mul_poly [([], (-1)%Z)] (expr_to_poly e1)
  end.

Fixpoint poly_to_expr_vars (v : list positive) : Expr :=
  match v with
  | [] => Const 1%Z
  | [x] => Var x
  | x :: xs => Mult (Var x) (poly_to_expr_vars xs)
  end.

Definition poly_to_expr_term (v : list positive) (c : Z) : Expr :=
  match v with
  | [] => Const c
  | _ =>
      if Z.eqb c 1%Z then poly_to_expr_vars v
      else if Z.eqb c (-1)%Z then Neg (poly_to_expr_vars v)
      else Mult (Const c) (poly_to_expr_vars v)
  end.

Fixpoint poly_to_expr (p : Poly) : Expr :=
  match p with
  | [] => Const 0%Z
  | [(v, c)] => poly_to_expr_term v c
  | (v, c) :: ps => Add (poly_to_expr_term v c) (poly_to_expr ps)
  end.

Definition polynomial_simplify (e : Expr) : Expr :=
  poly_to_expr (expr_to_poly e).

Fixpoint expr_eqb (e1 e2 : Expr) : bool :=
  match e1, e2 with
  | Var v1, Var v2 => Pos.eqb v1 v2
  | Const c1, Const c2 => Z.eqb c1 c2
  | Mult l1 r1, Mult l2 r2 => expr_eqb l1 l2 && expr_eqb r1 r2
  | Add l1 r1, Add l2 r2 => expr_eqb l1 l2 && expr_eqb r1 r2
  | Neg e1', Neg e2' => expr_eqb e1' e2'
  | _, _ => false
  end.

Coercion Const : Z >-> Expr.

Notation "x == y" := (expr_eqb x y) (at level 70, no associativity).

Fixpoint eval_vars (env : Env) (v : list positive) : Z :=
  match v with
  | [] => 1%Z
  | x :: xs => (get_env env x * eval_vars env xs)%Z
  end.

Fixpoint eval_poly (env : Env) (p : Poly) : Z :=
  match p with
  | [] => 0%Z
  | (v, c) :: ps => (c * eval_vars env v + eval_poly env ps)%Z
  end.

Lemma eval_poly_to_expr_vars : forall env v,
  eval_expr env (poly_to_expr_vars v) = eval_vars env v.
Proof.
  intros env v.
  induction v as [| x xs H1].
  - simpl. reflexivity.
  - destruct xs as [| y ys].
    + simpl. rewrite Z.mul_1_r. reflexivity.
    + simpl in *. rewrite H1. reflexivity.
Qed.

Lemma poly_to_expr_term_cons : forall env x xs c,
  eval_expr env (poly_to_expr_term (x :: xs) c) = (c * eval_vars env (x :: xs))%Z.
Proof.
  intros env x xs c.
  unfold poly_to_expr_term.
  destruct (Z.eqb c 1) eqn:H1.
  - apply Z.eqb_eq in H1. subst.
    rewrite eval_poly_to_expr_vars. rewrite Z.mul_1_l. reflexivity.
  - destruct (Z.eqb c (-1)) eqn:H2.
    + apply Z.eqb_eq in H2. subst.
      replace (eval_expr env (Neg (poly_to_expr_vars (x :: xs))))
         with (- eval_expr env (poly_to_expr_vars (x :: xs)))%Z by reflexivity.
      rewrite eval_poly_to_expr_vars. ring.
    + replace (eval_expr env (Mult (Const c) (poly_to_expr_vars (x :: xs))))
         with (c * eval_expr env (poly_to_expr_vars (x :: xs)))%Z by reflexivity.
      rewrite eval_poly_to_expr_vars. ring.
Qed.

Lemma eval_poly_to_expr_term : forall env v c,
  eval_expr env (poly_to_expr_term v c) = (c * eval_vars env v)%Z.
Proof.
  intros env v c.
  destruct v as [| x xs].
  - simpl. ring.
  - apply poly_to_expr_term_cons.
Qed.

Lemma eval_poly_to_expr_cons : forall env v c ps,
  eval_expr env (poly_to_expr ((v, c) :: ps)) =
  (eval_expr env (poly_to_expr_term v c) + eval_expr env (poly_to_expr ps))%Z.
Proof.
  intros env v c ps.
  destruct ps as [| [v' c'] ps'].
  - simpl. ring.
  - simpl. reflexivity.
Qed.

Lemma var_list_compare_eq : forall v1 v2,
  var_list_compare v1 v2 = Eq -> v1 = v2.
Proof.
  intros v1.
  induction v1 as [| x xs H1]; intros v2 H2.
  - destruct v2; reflexivity || discriminate.
  - destruct v2 as [| y ys]; try discriminate.
    simpl in H2. destruct (Pos.compare x y) eqn:H3; try discriminate.
    apply Pos.compare_eq in H3. subst.
    apply H1 in H2. subst. reflexivity.
Qed.

Lemma eval_add_poly : forall env p1 p2,
  eval_poly env (add_poly p1 p2) = (eval_poly env p1 + eval_poly env p2)%Z.
Proof.
  intros env p1.
  induction p1 as [| [v1 c1] ps1 H1]; intros p2.
  - simpl. apply Z.add_0_l.
  - induction p2 as [| [v2 c2] ps2 H2].
    + simpl. rewrite Z.add_0_r. reflexivity.
    + simpl. destruct (var_list_compare v1 v2) eqn:H3.
      * apply var_list_compare_eq in H3. subst.
        destruct (Z.eqb (c1 + c2) 0) eqn:H4.
        -- apply Z.eqb_eq in H4. rewrite H1. simpl. lia.
        -- simpl. rewrite H1. simpl. ring.
      * change (eval_poly env ((v1, c1) :: add_poly ps1 ((v2, c2) :: ps2)) =
          (c1 * eval_vars env v1 + eval_poly env ps1 + (c2 * eval_vars env v2 + eval_poly env ps2))%Z).
        simpl eval_poly. rewrite H1. simpl. ring.
      * change (eval_poly env ((v2, c2) :: add_poly ((v1, c1) :: ps1) ps2) =
          (c1 * eval_vars env v1 + eval_poly env ps1 + (c2 * eval_vars env v2 + eval_poly env ps2))%Z).
        change ((c2 * eval_vars env v2 + eval_poly env (add_poly ((v1, c1) :: ps1) ps2))%Z =
        (c1 * eval_vars env v1 + eval_poly env ps1 + (c2 * eval_vars env v2 + eval_poly env ps2))%Z).
        rewrite H2. simpl. ring.
Qed.

Lemma eval_merge_vars : forall env v1 v2,
  eval_vars env (merge_vars v1 v2) = (eval_vars env v1 * eval_vars env v2)%Z.
Proof.
  intros env v1.
  induction v1 as [| x xs H1]; intros v2.
  - change (eval_vars env v2 = (1 * eval_vars env v2)%Z). ring.
  - induction v2 as [| y ys H2].
    + change (eval_vars env (x :: xs) = (eval_vars env (x :: xs) * 1)%Z). ring.
    + simpl merge_vars. destruct (Pos.compare x y) eqn:H3.
      * change ((get_env env y * eval_vars env (merge_vars (x :: xs) ys))%Z =
          ((get_env env x * eval_vars env xs) * (get_env env y * eval_vars env ys))%Z).
        rewrite H2. simpl. ring.
      * change ((get_env env x * eval_vars env (merge_vars xs (y :: ys)))%Z =
          ((get_env env x * eval_vars env xs) * (get_env env y * eval_vars env ys))%Z).
        rewrite H1. simpl. ring.
      * change ((get_env env y * eval_vars env (merge_vars (x :: xs) ys))%Z =
          ((get_env env x * eval_vars env xs) * (get_env env y * eval_vars env ys))%Z).
        rewrite H2. simpl. ring.
Qed.

Lemma eval_mul_term_poly : forall env v c p,
  eval_poly env (mul_term_poly v c p) = (c * eval_vars env v * eval_poly env p)%Z.
Proof.
  intros env v c p.
  induction p as [| [v' c'] ps H1].
  - simpl. ring.
  - simpl mul_term_poly. destruct (Z.eqb (c * c') 0) eqn:H2.
    + apply Z.eqb_eq in H2. simpl eval_poly. rewrite H1.
      replace (c * eval_vars env v * (c' * eval_vars env v' + eval_poly env ps))%Z
         with (c * c' * eval_vars env v * eval_vars env v' + c * eval_vars env v * eval_poly env ps)%Z by ring.
      rewrite H2. ring.
    + change (eval_poly env (add_poly [(merge_vars v v', c * c')] (mul_term_poly v c ps)) =
        (c * eval_vars env v * eval_poly env ((v', c') :: ps))%Z).
      rewrite eval_add_poly. simpl eval_poly. rewrite eval_merge_vars, H1. ring.
Qed.

Lemma eval_mul_poly : forall env p1 p2,
  eval_poly env (mul_poly p1 p2) = (eval_poly env p1 * eval_poly env p2)%Z.
Proof.
  intros env p1 p2.
  induction p1 as [| [v c] ps H1].
  - simpl. ring.
  - simpl. rewrite eval_add_poly, eval_mul_term_poly, H1. ring.
Qed.

Lemma eval_expr_to_poly : forall env e,
  eval_poly env (expr_to_poly e) = eval_expr env e.
Proof.
  intros env e.
  induction e as [v | c | e1 H1 e2 H2 | e1 H1 e2 H2 | e1 H1].
  - change ((1 * (get_env env v * 1) + 0)%Z = get_env env v). ring.
  - unfold expr_to_poly. destruct (Z.eqb c 0) eqn:H1.
    + apply Z.eqb_eq in H1. subst. reflexivity.
    + change ((c * 1 + 0)%Z = c). ring.
  - unfold expr_to_poly; fold expr_to_poly. simpl eval_expr. rewrite eval_mul_poly, H1, H2. reflexivity.
  - unfold expr_to_poly; fold expr_to_poly. rewrite eval_add_poly, H1, H2. reflexivity.
  - unfold expr_to_poly; fold expr_to_poly. rewrite eval_mul_poly, H1.
    change (eval_poly env [([], -1)]) with (-1 * 1 + 0)%Z. simpl eval_expr. ring.
Qed.

Lemma eval_poly_to_expr : forall env p,
  eval_expr env (poly_to_expr p) = eval_poly env p.
Proof.
  intros env p.
  induction p as [| [v c] ps H1].
  - simpl. reflexivity.
  - rewrite eval_poly_to_expr_cons.
    rewrite eval_poly_to_expr_term.
    rewrite H1.
    simpl. reflexivity.
Qed.

Theorem polynomial_simplify_correct : forall e env,
  eval_expr env (polynomial_simplify e) = eval_expr env e.
Proof.
  intros e env.
  unfold polynomial_simplify.
  rewrite eval_poly_to_expr.
  rewrite eval_expr_to_poly.
  reflexivity.
Qed.

Lemma expr_eqb_correct : forall e1 e2,
  expr_eqb e1 e2 = true -> forall env, eval_expr env e1 = eval_expr env e2.
Proof.
  intros e1.
  induction e1 as [v1 | c1 | l1 H1 r1 H2 | l1 H1 r1 H2 | e1' H1];
    intros e2 H3 env; destruct e2 as [v2 | c2 | l2 r2 | l2 r2 | e2'];
    try discriminate.
  - apply Pos.eqb_eq in H3. subst. reflexivity.
  - apply Z.eqb_eq in H3. subst. reflexivity.
  - apply andb_true_iff in H3. destruct H3 as [H4 H5].
    simpl. rewrite (H1 l2 H4 env). rewrite (H2 r2 H5 env). reflexivity.
  - apply andb_true_iff in H3. destruct H3 as [H4 H5].
    simpl. rewrite (H1 l2 H4 env). rewrite (H2 r2 H5 env). reflexivity.
  - simpl. rewrite (H1 e2' H3 env). reflexivity.
Qed.

Section Test.

Definition test_env : Env := 
  make_env [(1%positive, 5%Z); (2%positive, 7%Z)].

Compute (polynomial_simplify (Add (Mult (Var 1) (Var 2)) (Neg (Const 4)))).

Compute (eval_expr test_env (Add (Mult (Var 1) (Var 2)) (Neg (Const 4)))).

Compute (eval_expr test_env (polynomial_simplify (Add (Mult (Var 1) (Var 2)) (Neg (Const 4))))).

Compute (polynomial_simplify (Mult (Add (Var 1) (Const 1)) (Add (Var 1) (Neg (Const 1))))).

Compute (eval_expr test_env (Mult (Add (Var 1) (Const 1)) (Add (Var 1) (Neg (Const 1))))).

Compute (eval_expr test_env (polynomial_simplify (Mult (Add (Var 1) (Const 1)) (Add (Var 1) (Neg (Const 1)))))).

End Test.