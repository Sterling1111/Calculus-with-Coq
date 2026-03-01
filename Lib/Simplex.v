Require Import Imports.
Require Import PolySimp.
Require Import Psatz.

Open Scope Z_scope.

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

Ltac simplex_core :=
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

Tactic Notation "simplex" := negate_goal; simplex_core.

Lemma test_chain : forall x y z w : Z,
  x > y ->
  y > z ->
  z > w ->
  x >= w + 3.
Proof.
  simplex.
  Show Proof.
Qed.

Lemma gt_implies_succ_le :
  forall a b : Z, a > b -> b + 1 <= a.
Proof.
  intros a b H.
  unfold Z.gt in H.              (* H : b < a *)
  apply Z.lt_succ_r.             (* goal: b + 1 < a + 1 *)
  apply Z.add_lt_mono_r.         (* add 1 to both sides of b < a *)
  apply Z.compare_gt_iff.
  exact H.
Qed.

Theorem chain_gt_three :
  forall x y z w : Z,
    x > y -> y > z -> z > w -> x >= w + 3.
Proof.
  intros x y z w Hxy Hyz Hzw.

  (* Turn each strict inequality into a "+1 ≤" fact *)
  pose proof gt_implies_succ_le x y Hxy as Hy1.  (* y + 1 <= x *)
  pose proof gt_implies_succ_le y z Hyz as Hz1.  (* z + 1 <= y *)
  pose proof gt_implies_succ_le z w Hzw as Hw1.  (* w + 1 <= z *)

  (* From w+1 <= z and z+1 <= y, get w+2 <= y *)
  assert (Hw2 : w + 2 <= y).
  {
    replace (w + 2) with (w + (1 + 1)) by reflexivity.
    rewrite Z.add_assoc.
eapply Z.le_trans.
- apply Z.add_le_mono_r. exact Hw1.
- exact Hz1.
  }

  (* From w+2 <= y and y+1 <= x, get w+3 <= x *)
  assert (Hw3 : w + 3 <= x).
  {
    replace (w + 3) with (w + (2 + 1)) by reflexivity.
    rewrite Z.add_assoc.
    eapply Z.le_trans.
    - apply Z.add_le_mono_r. exact Hw2.  (* (w+2)+1 <= y+1 *)
    - exact Hy1.                          (* y+1 <= x *)
  }

  apply Z.le_ge.
apply Hw3.
Qed.



Lemma test_dense : forall a b c : Z,
  a + b >= 10 ->
  b + c >= 10 ->
  a + c >= 10 ->
  a + b + c >= 15.
Proof.
  Set Ltac Profiling.
  Time simplex.
  Show Ltac Profile.
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
  Set Ltac Profiling.
  Time simplex.
  Show Ltac Profile.
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
  simplex.
Qed.

Unset Ltac Profiling.

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
  Set Ltac Profiling.
  Time simplex.
  Show Ltac Profile.
Time Qed.