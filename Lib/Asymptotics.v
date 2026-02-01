From Lib Require Import Imports Notations Reals_util Functions Sums Sets 
      Sequence Exponential Trigonometry Binomial Continuity Interval Derivative Taylor.
Import SumNotations SequenceNotations FunctionNotations SetNotations IntervalNotations.

Open Scope R_scope.

Definition big_o (f g : ℕ -> ℝ) :=
  ∃ c N, c > 0 /\ ∀ (n : ℕ), n >= N -> |f n| <= c * |g n|.

Definition big_omega (f g : ℕ -> ℝ) :=
  ∃ c N, c > 0 /\ ∀ (n : ℕ), n >= N -> |f n| >= c * |g n|.

Definition big_theta (f g : ℕ -> ℝ) :=
  ∃ c1 c2 N, c1 > 0 /\ c2 > 0 /\ ∀ (n : ℕ), n >= N -> 
  c1 * |g n| <= |f n| <= c2 * |g n|.

Definition little_o (f g : ℕ -> ℝ) :=
  ∀ c, c > 0 -> ∃ N, ∀ (n : ℕ), n >= N -> |f n| <= c * |g n|.

Definition little_omega (f g : ℕ -> ℝ) :=
  ∀ c, c > 0 -> ∃ N, ∀ (n : ℕ), n >= N -> |f n| >= c * |g n|.

Notation "f = Ο( g )" := (big_o f g) 
  (at level 70, no associativity, format "f  =  Ο( g )") : R_scope.

Notation "f = Ω( g )" := (big_omega f g) 
  (at level 70, no associativity, format "f  =  Ω( g )") : R_scope.

Notation "f = Θ( g )" := (big_theta f g) 
  (at level 70, no associativity, format "f  =  Θ( g )") : R_scope.

Notation "f = o( g )" := (little_o f g) 
  (at level 70, no associativity, format "f  =  o( g )") : R_scope.

Notation "f = ω( g )" := (little_omega f g) 
  (at level 70, no associativity, format "f  =  ω( g )") : R_scope.

Lemma big_theta_iff (f g : ℕ -> ℝ) :
  f = Θ( g ) <-> (f = Ο( g ) /\ f = Ω( g )).
Proof.
  split.
  - intros [c1 [c2 [N [H1 [H2 H3]]]]]. split; 
    [exists c2, N | exists c1, N]; split; auto; intros n H4; 
    specialize (H3 n H4); lra.
  - intros [[c1 [N1 [H3 H4]]] [c2 [N2 [H5 H6]]]].
    set (N := Rmax N1 N2). exists c2, c1, N. split; [| split]; auto.
    intros n H7.
    specialize (H4 n ltac:(unfold N in *; solve_R)).
    specialize (H6 n ltac:(unfold N in *; solve_R)).
    lra.
Qed.

Lemma little_o_iff_limit_zero : forall f g,
  (forall n, g n <> 0) ->
  f = o(g) <-> ⟦ lim ⟧ (λ n, f n / g n) = 0.
Proof.
  intros f g H1. split.
  - intros H2 ε H3. specialize (H2 (ε/2) ltac:(lra)) as [N H4]. exists N. intros n H5.
    specialize (H4 n ltac:(solve_R)). rewrite Rminus_0_r. unfold Rdiv.
    rewrite Rabs_mult, Rabs_inv. specialize (H1 n).
    apply Rmult_lt_reg_r with (r := |g n|); [solve_R |].
    apply Rmult_le_compat_l with (r := 2) in H4; try lra.
    field_simplify in H4. field_simplify; solve_R.
  - intros H2 c H3. specialize (H2 (c/2) ltac:(lra)) as [N H4]. exists (N + 1). intros n H5.
    specialize (H4 n ltac:(solve_R)). rewrite Rminus_0_r in H4.
    unfold Rdiv in H4. rewrite Rabs_mult, Rabs_inv in H4.
    specialize (H1 n). apply Rmult_lt_compat_r with (r := |g n|) in H4; [| solve_R].
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r in H4; solve_R.
Qed.

Lemma little_omega_iff_limit_infty : forall f g,
  (forall n, g n <> 0) ->
  f = ω(g) <-> ⟦ lim ⟧ (λ n, |f n / g n|) = ∞.
Proof.
  intros f g H1. split.
  - intros H2 M. destruct (Rlt_dec M 0) as [H3 | H3].
    + exists 0%nat. solve_R.
    + specialize (H2 (M + 1) ltac:(lra)) as [N H4].
      exists N. intros n H5. specialize (H4 n ltac:(solve_R)).
      unfold Rdiv. rewrite Rabs_mult, Rabs_inv. specialize (H1 n).
      apply Rmult_lt_reg_r with (r := |g n|); [ solve_R |].
      rewrite Rmult_assoc, Rinv_l, Rmult_1_r; solve_R.
  - intros H2 c H3.
    specialize (H2 c) as [N H4].
    exists (N + 1). intros n H5. specialize (H4 n ltac:(solve_R)).
    unfold Rdiv in H4. rewrite Rabs_mult, Rabs_inv in H4.
    apply Rmult_lt_compat_r with (r := |g n|) in H4; [| apply Rabs_pos_lt; apply H1].
    rewrite Rmult_assoc, Rinv_l, Rmult_1_r in H4; solve_R.
Qed.
    
Theorem big_theta_trans : forall f g h,
  f = Θ( g ) -> g = Θ( h ) -> f = Θ( h ).
Proof.
  intros f g h [c1 [c2 [N1 [H1 [H2 H3]]]]] [d1 [d2 [N2 [H4 [H5 H6]]]]].
  set (N := Rmax N1 N2). exists (c1 * d1), (c2 * d2), N.
  split; [| split]; try nra.
  intros n H7. 
  specialize (H3 n ltac:(unfold N in *; solve_R)).
  specialize (H6 n ltac:(unfold N in *; solve_R)).
  nra.
Qed.

Theorem big_o_trans : forall f g h,
  f = Ο( g ) -> g = Ο( h ) -> f = Ο( h ).
Proof.
  intros f g h [c1 [N1 [H1 H2]]] [c2 [N2 [H3 H4]]].
  set (N := Rmax N1 N2). exists (c1 * c2), N.
  split; [nra |].
  intros n H5.
  specialize (H2 n ltac:(unfold N in *; solve_R)).
  specialize (H4 n ltac:(unfold N in *; solve_R)).
  nra.
Qed.

Theorem big_omega_trans : forall f g h,
  f = Ω( g ) -> g = Ω( h ) -> f = Ω( h ).
Proof.
  intros f g h [c1 [N1 [H1 H2]]] [c2 [N2 [H3 H4]]].
  set (N := Rmax N1 N2). exists (c1 * c2), N.
  split; [nra |].
  intros n H5.
  specialize (H2 n ltac:(unfold N in *; solve_R)).
  specialize (H4 n ltac:(unfold N in *; solve_R)).
  nra.
Qed.

Theorem little_o_trans : forall f g h,
  f = o( g ) -> g = o( h ) -> f = o( h ).
Proof.
  intros f g h H1 H2 c H3.
  specialize (H1 c H3) as [N1 H4].
  specialize (H2 1 ltac:(lra)) as [N2 H5].
  set (N := Rmax N1 N2). exists N.
  intros n H6.
  specialize (H4 n ltac:(unfold N in *; solve_R)).
  specialize (H5 n ltac:(unfold N in *; solve_R)).
  nra.
Qed.

Theorem little_omega_trans : forall f g h,
  f = ω( g ) -> g = ω( h ) -> f = ω( h ).
Proof.
  intros f g h H1 H2 c H3.
  specialize (H1 c H3) as [N1 H4].
  specialize (H2 1 ltac:(lra)) as [N2 H5].
  set (N := Rmax N1 N2). exists N.
  intros n H6.
  specialize (H4 n ltac:(unfold N in *; solve_R)).
  specialize (H5 n ltac:(unfold N in *; solve_R)).
  nra.
Qed.

Lemma big_o_theta_trans : forall f g h,
  f = Ο(g) -> g = Θ(h) -> f = Ο(h).
Proof.
  intros f g h H1 H2.
  apply big_o_trans with g; auto.
  apply big_theta_iff in H2. destruct H2; auto.
Qed.

Theorem big_theta_refl : forall f, f = Θ( f ).
Proof.
  intros f. exists 1, 1, 0%nat. repeat split; lra.
Qed.

Theorem big_o_refl : forall f, f = Ο( f ).
Proof.
  intros f. exists 1, 0%nat. split; solve_R.
Qed.

Lemma big_omega_refl : forall f, f = Ω( f ).
Proof.
  intros f. exists 1, 0%nat. split; solve_R.
Qed.

Theorem big_theta_sym : forall f g,
  f = Θ( g ) <-> g = Θ( f ).
Proof.
  intros f g. split; intros H1.
  - destruct H1 as [c1 [c2 [N [H2 [H3 H4]]]]].
    exists (1 / c2), (1 / c1), N. split; [| split]; try (apply Rdiv_pos_pos; lra).
    intros n H5. specialize (H4 n H5). split.
    + apply Rmult_le_reg_r with (r := c2); try lra. field_simplify; solve_R.
    + apply Rmult_le_reg_r with (r := c1); try lra. field_simplify; solve_R.
  - destruct H1 as [c1 [c2 [N [H2 [H3 H4]]]]].
    exists (1 / c2), (1 / c1), N. split; [| split]; try (apply Rdiv_pos_pos; lra).
    intros n H5. specialize (H4 n H5). split.
    + apply Rmult_le_reg_r with (r := c2); try lra. field_simplify; solve_R.
    + apply Rmult_le_reg_r with (r := c1); try lra. field_simplify; solve_R.
Qed.

Theorem transpose_sym_O_Omega : forall f g,
  f = Ο( g ) <-> g = Ω( f ).
Proof.
  intros f g. split; intros H1.
  - destruct H1 as [c [N [H2 H3]]]. 
    exists (1 / c), N. split; try (apply Rdiv_pos_pos; lra).
    intros n H4. specialize (H3 n H4). apply Rle_ge.
    apply Rmult_le_reg_r with (r := c); try lra. field_simplify; solve_R.
  - destruct H1 as [c [N [H2 H3]]].
    exists (1 / c), N. split; try (apply Rdiv_pos_pos; lra).
    intros n H4. specialize (H3 n H4).
    apply Rmult_le_reg_r with (r := c); try lra. field_simplify; solve_R.
Qed.

Theorem transpose_sym_o_omega : forall f g,
  f = o( g ) <-> g = ω( f ).
Proof.
  intros f g. split; intros H1.
  - intros c H2. specialize (H1 (1 / c) ltac:(apply Rdiv_pos_pos; lra)) as [N H3].
    exists N. intros n H4. specialize (H3 n H4). apply Rle_ge.
    apply Rmult_le_compat_l with (r := c) in H3; try lra.
    field_simplify in H3; solve_R.
  - intros c H2. specialize (H1 (1 / c) ltac:(apply Rdiv_pos_pos; lra)) as [N H3].
    exists N. intros n H4. specialize (H3 n H4). apply Rge_le in H3.
    apply Rmult_le_compat_l with (r := c) in H3; try lra.
    field_simplify in H3; solve_R.
Qed.

Lemma big_o_canonical_reduction : forall f f' g g',
  f = Θ(f') ->
  g = Θ(g') ->
  f' = Ο(g') ->
  f = Ο(g).
Proof.
  intros f f' g g' H1 H2 H3.
  apply big_o_trans with f'.
  - apply big_theta_iff in H1; destruct H1; auto.
  - apply big_o_trans with g'; auto.
    apply big_theta_iff in H2; destruct H2 as [_ H2].
    apply transpose_sym_O_Omega; auto.
Qed.

Lemma big_omega_canonical_reduction : forall f f' g g',
  f = Θ(f') ->
  g = Θ(g') ->
  f' = Ω(g') ->
  f = Ω(g).
Proof.
  intros f f' g g' H1 H2 H3.
  apply transpose_sym_O_Omega.
  apply big_o_canonical_reduction with (f' := g') (g' := f'); auto.
  apply transpose_sym_O_Omega; auto.
Qed.

Lemma big_theta_canonical_reduction : forall f f' g g',
  f = Θ(f') ->
  g = Θ(g') ->
  f' = Θ(g') ->
  f = Θ(g).
Proof.
  intros f f' g g' H1 H2 H3.
  apply big_theta_trans with f'; auto.
  apply big_theta_trans with g'; auto.
  apply big_theta_sym; auto.
Qed.

Lemma big_o_ext : forall f1 f2 g1 g2,
  (forall n, f1 n = f2 n) -> (forall n, g1 n = g2 n) -> f2 = Ο(g2) -> f1 = Ο(g1).
Proof.
  intros f1 f2 g1 g2 H1 H2 H3.
  replace f1 with f2 by (extensionality n; rewrite H1; reflexivity).
  replace g1 with g2 by (extensionality n; rewrite H2; reflexivity).
  auto.
Qed.

Lemma big_omega_ext : forall f1 f2 g1 g2,
  (forall n, f1 n = f2 n) -> (forall n, g1 n = g2 n) -> f2 = Ω(g2) -> f1 = Ω(g1).
Proof.
  intros f1 f2 g1 g2 H1 H2 H3.
  replace f1 with f2 by (extensionality n; rewrite H1; reflexivity).
  replace g1 with g2 by (extensionality n; rewrite H2; reflexivity).
  auto.
Qed.

Lemma big_theta_ext : forall f1 f2 g1 g2,
  (forall n, f1 n = f2 n) -> (forall n, g1 n = g2 n) -> f2 = Θ(g2) -> f1 = Θ(g1).
Proof.
  intros f1 f2 g1 g2 H1 H2 H3.
  replace f1 with f2 by (extensionality n; rewrite H1; reflexivity).
  replace g1 with g2 by (extensionality n; rewrite H2; reflexivity).
  auto.
Qed.

Lemma big_o_const : forall c,
  c > 0 -> (λ n, c) = Ο(λ n, 1).
Proof.
  intros c H1. exists c, 0%nat. split; solve_R.
Qed.

Lemma big_omega_const : forall c,
  c > 0 -> (λ n, c) = Ω(λ n, 1).
Proof.
  intros c H1. exists c, 0%nat. split; solve_R.
Qed.

Lemma big_theta_const : forall c,
  c > 0 -> (λ n, c) = Θ(λ n, 1).
Proof.
  intros c H1.
  apply big_theta_iff. split.
  - apply big_o_const; auto.
  - apply big_omega_const; auto.
Qed.

Inductive expr : Type :=
| EConst (c : R)
| EVar
| EAdd (e1 e2 : expr)
| ESub (e1 e2 : expr)
| EMult (e1 e2 : expr)
| EDiv (e1 e2 : expr)
| EPow (b : expr) (e : R).

Fixpoint eval (e : expr) (n : nat) : R :=
  match e with
  | EConst c => c
  | EVar => INR n
  | EAdd e1 e2 => eval e1 n + eval e2 n
  | ESub e1 e2 => eval e1 n - eval e2 n
  | EMult e1 e2 => eval e1 n * eval e2 n
  | EDiv e1 e2 => eval e1 n / eval e2 n
  | EPow b e => Rpower (eval b n) e
  end.

Fixpoint wf_expr (e : expr) (n : nat) : Prop :=
  match e with
  | EConst c => c > 0
  | EVar => True
  | EAdd e1 e2 | EMult e1 e2 => wf_expr e1 n /\ wf_expr e2 n
  | ESub e1 e2 => wf_expr e1 n /\ wf_expr e2 n
  | EDiv e1 e2 => wf_expr e1 n /\ wf_expr e2 n /\ eval e2 n <> 0
  | EPow b e => wf_expr b n /\ eval b n > 0
  end.

Fixpoint get_degree (e : expr) : R :=
  match e with
  | EConst _ => 0
  | EVar => 1
  | EAdd e1 e2 | ESub e1 e2 => Rmax (get_degree e1) (get_degree e2)
  | EMult e1 e2 => get_degree e1 + get_degree e2
  | EDiv e1 e2 => get_degree e1 - get_degree e2
  | EPow b e => get_degree b * e
  end.

Fixpoint reduce (e : expr) : expr :=
  match e with
  | EConst _ => EConst 1
  | EVar => EVar
  | EAdd e1 e2 => 
      let d1 := get_degree e1 in
      let d2 := get_degree e2 in
      if Rlt_dec d1 d2 then reduce e2 
      else if Rlt_dec d2 d1 then reduce e1 
      else EAdd (reduce e1) (reduce e2)
  | ESub e1 e2 =>
      let d1 := get_degree e1 in
      let d2 := get_degree e2 in
      if Rlt_dec d2 d1 then reduce e1 else ESub (reduce e1) (reduce e2)
  | EMult e1 e2 => EMult (reduce e1) (reduce e2)
  | EDiv e1 e2 => EDiv (reduce e1) (reduce e2)
  | EPow b e => EPow (reduce b) e
  end.

Ltac reify_constant n c :=
  lazymatch c with
  | context[n] => fail "reify_constant: Term depends on variable" n ":" c
  | _ =>
      lazymatch type of c with
      | R => constr:(EConst c)
      | Z => let r := constr:(IZR c) in constr:(EConst r)
      | nat => let r := constr:(IZR (Z.of_nat c)) in constr:(EConst r)
      | _ => fail "reify_constant: Cannot parse type:" c
      end
  end.

Ltac get_real_value c :=
  lazymatch type of c with
  | R => constr:(c)
  | Z => constr:(IZR c)
  | nat => constr:(IZR (Z.of_nat c))
  | _ => fail "get_real_value: Cannot parse exponent:" c
  end.

Ltac reify_expr n t :=
  lazymatch t with
  | INR n => constr:(EVar)
  | n => constr:(EVar)
  | context[n] =>
      lazymatch t with
      | ?u + ?v => let e1 := reify_expr n u in let e2 := reify_expr n v in constr:(EAdd e1 e2)
      | ?u - ?v => let e1 := reify_expr n u in let e2 := reify_expr n v in constr:(ESub e1 e2)
      | ?u * ?v => let e1 := reify_expr n u in let e2 := reify_expr n v in constr:(EMult e1 e2)
      | ?u / ?v => let e1 := reify_expr n u in let e2 := reify_expr n v in constr:(EDiv e1 e2)
      | ?b ^ ?k => 
          let eb := reify_expr n b in 
          let rk := get_real_value k in
          constr:(EPow eb rk)
      | Rpower ?b ?k => 
          let eb := reify_expr n b in 
          let rk := get_real_value k in
          constr:(EPow eb rk)
      | INR ?u => reify_expr n u
      | _ => reify_constant n t
      end
  | _ => reify_constant n t
  end.

Ltac change_fun_to_expr :=
  let reify_side f :=
    let n := fresh "n" in intros n;
    let fn := eval cbv beta in (f n) in
    let e := reify_expr n fn in
    instantiate (1 := fun k => eval e k); simpl; reflexivity
  in
  lazymatch goal with
  | |- ?f = Ο( ?g ) => eapply big_o_ext; [ reify_side f | reify_side g | ]
  | |- ?f = Ω( ?g ) => eapply big_omega_ext; [ reify_side f | reify_side g | ]
  | |- ?f = Θ( ?g ) => eapply big_theta_ext; [ reify_side f | reify_side g | ]
  end.

Definition eventually_wf (e : expr) := exists N, forall n, (n >= N)%nat -> wf_expr e n.

Lemma big_o_plus : forall f1 f2 g,
  f1 = Ο(g) -> f2 = Ο(g) -> (λ n, f1 n + f2 n) = Ο(g).
Proof.
  intros f1 f2 g [c1 [N1 [H1 H2]]] [c2 [N2 [H3 H4]]].
  exists (c1 + c2), (Rmax N1 N2). split; [lra |].
  intros n H5.
  apply Rle_trans with (|f1 n| + |f2 n|); [apply Rabs_triang |].
  rewrite Rmult_plus_distr_r.
  apply Rplus_le_compat.
  - apply H2; apply Rle_ge; apply Rle_trans with (Rmax N1 N2); [apply Rmax_l | apply Rge_le; exact H5].
  - apply H4; apply Rle_ge; apply Rle_trans with (Rmax N1 N2); [apply Rmax_r | apply Rge_le; exact H5].
Qed.

Lemma big_omega_plus : forall f1 f2 g,
  (forall n, f1 n >= 0) -> 
  (forall n, f2 n >= 0) ->
  f1 = Ω(g) -> f2 = Ω(g) -> (λ n, f1 n + f2 n) = Ω(g).
Proof.
  intros f1 f2 g H1 H2 [c1 [N1 [H3 H4]]] [c2 [N2 [H5 H6]]].
  exists (c1 + c2), (Rmax 0 (Rmax N1 N2)). split; [lra |].
  intros n H7. apply Rle_ge.
  apply Rle_trans with (|f1 n| + |f2 n|).
  2 : { specialize (H1 n). specialize (H2 n). solve_R. }
  specialize (H4 n ltac:(solve_R)).
  specialize (H6 n ltac:(solve_R)).
  solve_R.
Qed.

Lemma big_theta_plus : forall f1 f2 g,
  (forall n, f1 n >= 0) ->
  (forall n, f2 n >= 0) ->
  f1 = Θ(g) -> f2 = Θ(g) -> (λ n, f1 n + f2 n) = Θ(g).
Proof.
  intros f1 f2 g H1 H2 H3 H4.
  apply big_theta_iff. split.
  - apply big_o_plus;
    apply big_theta_iff in H3; destruct H3; auto;
    apply big_theta_iff in H4; destruct H4; auto.
  - apply big_omega_plus; auto;
    apply big_theta_iff in H3; destruct H3; auto;
    apply big_theta_iff in H4; destruct H4; auto.
Qed.

Lemma reduce_valid : forall e, 
  eventually_wf e ->
  (fun n => eval e n) = Θ(fun n => eval (reduce e) n).
Proof.
  intros e [N H1]. induction e as 
  [c | | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | b IH k]; simpl.
  - apply big_theta_const. specialize (H1 N ltac:(solve_R)). auto.
  - apply big_theta_refl.
  - destruct (Rlt_dec (get_degree e1) (get_degree e2)) as [Hl | Hl].
    + apply big_theta_plus; admit.
    + admit.
  - admit.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma degree_correct : forall e, 
  eventually_wf e ->
  (fun n => eval (reduce e) n) = Θ(fun n => Rpower (INR n) (get_degree (reduce e))).
Proof. Admitted.

Lemma rpower_big_o : forall d1 d2, d1 <= d2 -> (fun n => Rpower (INR n) d1) = Ο(fun n => Rpower (INR n) d2).
Proof. Admitted.

Lemma rpower_big_omega : forall d1 d2, d1 >= d2 -> (fun n => Rpower (INR n) d1) = Ω(fun n => Rpower (INR n) d2).
Proof. Admitted.

Lemma rpower_big_theta : forall d1 d2, d1 = d2 -> (fun n => Rpower (INR n) d1) = Θ(fun n => Rpower (INR n) d2).
Proof. Admitted.

Lemma big_theta_iff_both_big_o : forall f g,
  f = Θ(g) <-> (f = Ο(g) /\ g = Ο(f)).
Proof.
  intros f g.
  rewrite big_theta_iff.
  rewrite transpose_sym_O_Omega.
  split; intros [H1 H2]; split; auto;
  apply transpose_sym_O_Omega; auto.
Qed.

Lemma big_theta_iff_both_big_omega : forall f g,
  f = Θ(g) <-> (f = Ω(g) /\ g = Ω(f)).
Proof.
  intros f g.
  rewrite big_theta_iff.
  split; intros [H1 H2]; split; auto;
  apply transpose_sym_O_Omega; auto.
Qed.


Lemma big_o_mult : forall f1 f2 g1 g2,
  f1 = Ο( g1 ) -> f2 = Ο( g2 ) -> (λ n, f1 n * f2 n) = Ο( λ n, g1 n * g2 n ).
Proof.
  intros f1 f2 g1 g2 [c1 [N1 [H1 H2]]] [c2 [N2 [H3 H4]]].
  exists (c1 * c2), (Rmax N1 N2). split; [nra |].
  intros n H5. rewrite Rabs_mult, Rabs_mult.
  specialize (H2 n ltac:(solve_R)).
  specialize (H4 n ltac:(solve_R)).
  solve_R.
Qed.

Lemma big_o_pow : forall f g k,
  f = Ο( g ) -> (λ n, (f n) ^ k) = Ο( λ n, (g n) ^ k ).
Proof.
  intros f g k H1. induction k as [| k IH].
  - exists 1, 0%nat. split; [lra |]. intros n H2. 
    simpl. rewrite Rabs_R1. lra.
  - simpl. apply big_o_mult; auto.
Qed.

Lemma big_o_poly_poly : forall p q,
  p <= q -> (λ n, n ^^ p) = Ο( λ n, n ^^ q ).
Proof.
  intros p q H1. exists 1, 1%nat. split; [lra |].
  intros n H2. rewrite Rmult_1_l.
  repeat rewrite Rabs_right; try apply Rpower_ge_0.
  apply Rpower_exp_le; solve_R.
Qed.

Lemma big_o_log_b_log_b : forall b1 b2,
  b1 > 1 -> b2 > 1 ->
  (log_ b1) = Ο( log_ b2 ).
Proof.
  intros b1 b2 H1 H2.
  exists (log b2 / log b1), 1%nat.
  split.
  - apply Rdiv_pos_pos; apply log_pos; auto.
  - intros n H3. 
    rewrite (log_change_base b1 b2 (INR n) H1 H2).
    pose proof log_pos b2 H2 as H4.
    pose proof log_pos b1 H1 as H5.
    pose proof log_b_nonneg b2 n H2 ltac:(solve_R) as H6.
    pose proof Rdiv_pos_pos (log b2) (log b1) H4 H5 as H7.
    solve_R.
Qed.

Lemma big_o_const_const : forall c1 c2,
  c1 > 0 -> c2 > 0 ->
  (λ n, c1) = Ο(λ n, c2).
Proof.
  intros c1 c2 H1 H2.
  destruct (Rle_dec c1 c2) as [H3 | H3].
  - exists 1, 0%nat. split; solve_R.
  - exists (c1 / c2), 0%nat. split; [apply Rdiv_pos_pos; solve_R |].
    intros n H4. apply Rmult_le_reg_r with (r := c2); field_simplify; solve_R.
Qed.

Lemma big_o_const_log : ∀ c b : ℝ, c > 0 → b > 1 → (λ _ : ℕ, c) = Ο(λ x : ℕ, log_ b x).
Proof.
  intros c b H1 H2.
  unfold big_o.
  exists c, b. split; [solve_R |].
  intros n H3. pose proof log_b_ge_1 b n H2 ltac:(lra). solve_R.
Qed.

Lemma big_o_log_poly : forall b k, 
  b > 1 -> k > 0 -> 
  (λ n, log_ b n) = Ο(λ n, n ^^ k).
Proof.
  intros b k H1 H2.
  exists (1 / (k * log b)), 1%nat. split.
  { apply Rdiv_pos_pos; [solve_R | apply Rmult_pos_pos; [solve_R | apply log_pos; auto]]. }
  intros n H3.
  rewrite Rabs_right; [| apply log_b_nonneg; auto; solve_R].
  rewrite Rabs_right; [| apply Rpower_ge_0; solve_R].
  apply Rmult_le_reg_r with (r := k * log b); [ pose proof log_pos b H1; solve_R |].
  field_simplify. 2 : { pose proof log_pos b H1; solve_R. }
  unfold log_.
  replace (log (INR n) / log b * k * log b) with (log ((INR n) ^^ k)).
  2: { unfold Rpower. destruct (Rlt_dec 0 n) as [H4 | H4].
       2 : { exfalso; apply H4. apply INR_ge in H3. solve_R. }
       rewrite log_exp. field. apply Rgt_not_eq; apply log_pos; lra. }
  set (y := n ^^ k).
  assert (H4 : y >= 1).
  {
    unfold y. destruct (Req_dec (INR n) 1) as [H4 | H4].
    - rewrite H4; rewrite Rpower_1_base; lra.
    - apply Rgt_ge. apply Rpower_gt_1; [ apply INR_ge in H3 |]; solve_R.
  }
  apply Rlt_le.
  apply log_lt_self; auto.
Qed.

Lemma big_o_log_of_poly : forall b c k,
  b > 1 -> c > 0 -> k > 0 ->
  (λ n, log_ b (n ^^ k)) = Ο(log_ b).
Proof.
  intros b c k H1 H2 H3.
  exists k, 1%nat. split; auto.
  intros n H4.
  rewrite Rabs_right.
  2 : { apply log_b_nonneg; auto. apply Rpower_ge_1; solve_R. }
  rewrite Rabs_right.
  2 : { apply log_b_nonneg; auto; solve_R. }
  unfold log_, Rpower.
  destruct (Rlt_dec 0 n) as [H5 | H5].
  - rewrite log_exp; lra.
  - apply INR_ge in H4. solve_R.
Qed.

Lemma big_omega_log_of_poly : forall b c k,
  b > 1 -> c > 0 -> k > 0 ->
  (λ n, log_ b (n ^^ k)) = Ω(log_ b).
Proof.
  intros b c k H1 H2 H3.
  exists k, 1%nat. split; auto.
  intros n H4.
  rewrite Rabs_right.
  2 : { apply log_b_nonneg; auto. apply Rpower_ge_1; solve_R. }
  rewrite Rabs_right.
  2 : { apply log_b_nonneg; auto; solve_R. }
  unfold log_, Rpower.
  destruct (Rlt_dec 0 n) as [H5 | H5].
  - rewrite log_exp; lra.
  - apply INR_ge in H4. solve_R.
Qed.

Lemma big_theta_log_of_poly : forall b c k,
  b > 1 -> c > 0 -> k > 0 ->
  (λ n, log_ b (n ^^ k)) = Θ(log_ b).
Proof.
  intros b c k H1 H2 H3. apply big_theta_iff; split.
  - apply big_o_log_of_poly with (c := c); auto.
  - apply big_omega_log_of_poly with (c := c); auto.
Qed.

Lemma big_o_log_le_log_pow : forall b c k,
  b > 1 -> c > 0 -> k > 0 ->
  (log_ b) = Ο(λ n, log_ b (n ^^ k)).
Proof.
  intros b c k H1 H2 H3.
  apply big_theta_iff. 
  apply big_theta_sym.
  apply big_theta_log_of_poly with (c := c); auto.
Qed.

Lemma big_o_poly_exp : forall k b,
  k > 0 -> b > 1 ->
  (λ n, n ^^ k) = Ο(λ n, b ^^ n).
Proof.
  intros k b H1 H2.
  destruct (INR_unbounded (Rmax 1 (k / log b))) as [N H3].
  exists (N ^^ k * b ^^ (-N)), N. split.
  - apply Rmult_pos_pos; [apply Rpower_gt_0 | apply Rpower_gt_0]; solve_R.
  - intros n H4.
    rewrite Rabs_right; [| apply Rpower_ge_0; solve_R].
    rewrite Rabs_right; [| apply Rpower_ge_0; solve_R].
    rewrite Rmult_assoc, <- Rpower_plus; try lra.
    replace (-N + n) with (n - N) by lra.
    rewrite <- (exp_log (n ^^ k)); [| apply Rpower_gt_0; solve_R].
    rewrite <- (exp_log (_ * _)); [ | apply Rmult_pos_pos; apply Rpower_gt_0; solve_R ].
    apply exp_nondecreasing; try apply Full_intro.
    rewrite theorem_18_1; [| apply Rpower_gt_0; solve_R | apply Rpower_gt_0; lra].
    unfold Rpower.
    destruct (Rlt_dec 0 n) as [H5 | H5]; [| solve_R].
    destruct (Rlt_dec 0 N) as [H6 | H6]; [| solve_R].
    destruct (Rlt_dec 0 b) as [H7 | H7]; [| lra].

    repeat rewrite log_exp.

    set (f := λ x, k * log x - x * log b).
    assert (H8 : decreasing_on f [N, n]).
    {
      destruct H4 as [H4 | H4]; [ | intros x y; rewrite H4; solve_R ].
      apply derivative_on_neg_imp_decreasing_on with (f' := λ x, k / x - log b); try lra.
      - apply derivative_on_eq with (f1 := f); auto.
        apply derivative_on_minus.
        * apply differentiable_domain_closed; auto.
        * apply derivative_on_mult_const_l; [apply differentiable_domain_closed; solve_R |].
          replace RinvImpl.Rinv with (λ x, 1 / x). 2 : { extensionality x. lra. }
          apply derivative_log_on; solve_R.
        * apply derivative_on_ext with (f1' := λ x, 1 * log b).
          { intros x H8. lra. }
          apply derivative_on_mult_const_r; [apply differentiable_domain_closed; solve_R |].
          apply derivative_on_id; apply differentiable_domain_closed; solve_R.
      - intros x H8.
       apply Rlt_minus.
      apply Rle_lt_trans with (k / INR N).
      + apply Rmult_le_compat_l; [lra |].
        apply Rinv_le_contravar; solve_R.
      + apply Rmult_lt_reg_r with (r := N); auto. field_simplify; try lra.
        assert (H9 : N > k / log b) by solve_R.
        pose proof log_pos b H2 as H10.
        apply Rmult_gt_compat_r with (r := log b) in H9; auto.
        field_simplify in H9; try lra.
    }
    destruct H4 as [H4 | H4].
    + specialize (H8 N n ltac:(solve_R) ltac:(solve_R) ltac:(lra)). unfold f in H8. lra.
    + rewrite H4. lra.
Qed.

Lemma big_o_exp_fact : forall b,
  b > 1 -> (λ n, b ^^ (INR n)) = Ο(λ n, INR (fact n)).
Proof.
  intros b H1.
  destruct (INR_unbounded b) as [N H2].
  exists (b ^ N), N. split; [apply pow_lt; lra |].
  intros n H3.
  rewrite Rabs_right; [| apply Rpower_ge_0].
  rewrite Rabs_right; [| apply Rle_ge; apply pos_INR].
  rewrite Rpower_nat; [| lra].
  induction n as [| k IH].
  - simpl. rewrite Rmult_1_r. apply Rlt_le, Rlt_pow_R1; try apply INR_lt; solve_R.
  - assert ((S k = N)%nat \/ (k >= N)%nat) as [H4 | H4] by (apply INR_ge in H3; lia).
    + rewrite H4. pose proof INR_fact_ge_1 N as H5. pose proof Rpow_gt_0 N b ltac:(lra) as H6. nra.
    + specialize (IH ltac:(solve_R)). 
      simpl. solve_R.
      apply Rle_trans with (b * (b ^ N * INR (fact k))).
* apply Rmult_le_compat_l; [lra | apply IH].
* replace (b * (b ^ N * k!)) with (b^N * (b * k!)) by lra.
  apply Rmult_le_compat_l; [ apply pow_le; lra |].
  replace (k! + k * k!) with ((1 + k) * k!) by lra.
  apply Rmult_le_compat_r; [apply pos_INR |].
  apply Rle_trans with k; solve_R.
Qed.

Lemma big_o_mult_const : forall f g c,
  c > 0 ->
  f = Ο(g) -> (λ n, c * f n) = Ο(g).
Proof.
  intros f g c H1 [c0 [N [H2 H3]]].
  exists (c * c0), N. split; [nra |].
  intros n H4.
  rewrite Rabs_mult, Rabs_right; [| nra].
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l; [nra | apply H3; auto].
Qed.

Lemma big_o_extend_1 : forall (f : nat -> R) (g : nat -> R) (N : R) (c : R),
  (forall n, (n >= 1)%nat -> g n > 0) ->
  (forall n : nat, n >= N -> f n <= c * g n) ->
  exists c', forall n, (n >= 1)%nat -> f n <= c' * g n.
Proof.
  intros f g N c H1 H2.
  set (k := Z.to_nat (up N)).
  assert (H3: exists x, forall n, (1 <= n <= k)%nat -> f n <= x * g n).
  { induction k as [|k [x H3]].
    - exists 0; intros n H3; lia.
    - exists (Rmax x (f (S k) / g (S k))); intros n H4.
      destruct (eq_nat_dec n (S k)) as [H5|H5].
      + rewrite H5; apply Rle_trans with ((f (S k) / g (S k)) * g (S k)); [|apply Rmult_le_compat_r; [apply Rlt_le, H1; lia|apply Rmax_r]].
        right; field. specialize (H1 (S k) ltac:(solve_R)). solve_R.
      + apply Rle_trans with (x * g n); [apply H3; lia|].
        apply Rmult_le_compat_r; [apply Rlt_le, H1; lia|apply Rmax_l]. }
  destruct H3 as [x H3]; exists (Rmax c x); intros n H4.
  destruct (le_gt_dec n k) as [H5|H5].
  - apply Rle_trans with (x * g n); [apply H3; lia|].
    apply Rmult_le_compat_r; [apply Rlt_le, H1; lia|apply Rmax_r].
  - apply Rle_trans with (c * g n); [apply H2|apply Rmult_le_compat_r; [apply Rlt_le, H1; lia|apply Rmax_l]].
    apply Rle_ge, Rlt_le, Rlt_le_trans with (IZR (up N)); [apply archimed | rewrite INR_IZR_INZ; apply IZR_le; lia].
Qed.

Lemma floor_power_bound : forall p : R, 
  exists k : R, k > 0 /\ forall x : R, x >= 1 -> ⌊x⌋^^p <= k * x^^p.
Proof.
  intro p. destruct (Rle_dec 0 p) as [H1|H1].
  - exists 1; split; [lra |].
    intros x H2. rewrite Rmult_1_l.
    apply Rpower_le; pose proof floor_spec x ltac:(lra); lra.
  - exists (2 ^^ (-p)); split; [apply Rpower_gt_0; lra |].
    intros x H2.
    assert (H3 : 0 < -p) by (apply Rlt_0_minus ; lra).
    assert (H4 : x <= 2 * ⌊x⌋).
    {
      pose proof floor_spec x ltac:(lra) as [H4 H5].
      destruct (⌊x⌋). simpl in *; try nra. rewrite S_INR in *.
      pose proof pos_INR n; lra.
    }
    replace (2 ^^ (- p) * x ^^ p) with ((x / 2) ^^ p).
    2: {
      rewrite <- Rpower_inv; [| lra].
      rewrite <- Rpower_mult_distr; try lra.
      f_equal; lra.
    }
    apply Rpower_le_contravar; try lra.
Qed.

Section Master_Theorem.
  Variables (a b : ℝ) (f T T' : ℕ -> ℝ).

  Hypothesis H1 : a >= 1.
  Hypothesis H2 : b > 1.
  Hypothesis H3 : ∀ n, f n >= 0.
  Hypothesis H4 : ∀ n, T n >= 0.
  Hypothesis H5 : T 1 > 0.
  Hypothesis H6 : ∀ n : ℕ, n >= b -> T n = a * T (⌊n/b⌋) + f n.
  Hypothesis H7 : ∀ k : ℕ, T' k = T (⌊b^k⌋).

  Lemma lemma_4_2 : ∀ n : ℕ, (n > 0)%nat -> is_natural b ->
     T' n = a ^ n * T' 0 + ∑ 0 (n-1) (λ j, a ^ j * f (⌊b^(n-j)⌋)).
  Proof.
    intros n H8 H9. induction n as [| k IH]; try lia.
    assert ((k = 0)%nat \/ (k > 0)%nat) as [H10 | H10] by lia.
    - rewrite H10. sum_simpl. rewrite Rmult_1_r, H7, H7, pow_1, pow_O.
      pose proof floor_INR b H9 as H11. rewrite H6, H11, Rdiv_diag; lra.
    - replace (S k - 1)%nat with k by lia.
      rewrite H7, H6. 2 : { apply floor_power_succ_ge_base; auto. }
      rewrite floor_INR. 2 : { apply is_natural_pow; auto. }
      rewrite floor_power_succ_div; auto.
      rewrite <- H7, IH; auto.
      rewrite Rmult_plus_distr_l, <- Rmult_assoc, tech_pow_Rmult, r_mult_sum_f_i_n_f_l, Rplus_assoc.
      apply f_equal.
      rewrite (sum_f_split 0 0 k); try lia. rewrite sum_f_0_0, pow_O, Rmult_1_l, Nat.sub_0_r.
      rewrite (sum_f_reindex _ 1 k 1); try lia. rewrite Nat.sub_diag.
      rewrite Rplus_comm. apply f_equal.
      apply sum_f_equiv; try lia.
      intros j H11. replace (S k - (j + 1))%nat with (k - j)%nat by lia.
      replace (j + 1)%nat with (S j) by lia.
      rewrite <- Rmult_assoc, tech_pow_Rmult. reflexivity.
  Qed.

  Lemma lemma_4_2' : ∀ k : ℕ, (k > 0)%nat -> is_natural b ->
    let n := ⌊b ^ k⌋ in
    T n = n ^^ (log_ b a) * T 1 + 
          ∑ 0 (k - 1) (λ j, a ^ j * f (⌊n/b^j⌋)).
  Proof.
    intros k H8 H9 n. unfold n. rewrite <- H7.
    rewrite lemma_4_2; auto.
    fold n.
    replace (T' 0) with (T 1).
    2 : { rewrite H7, pow_O. replace 1 with (INR 1) by auto. rewrite floor_INR_id; auto. }
    f_equal.
    - unfold n. rewrite floor_INR. 2 : { apply is_natural_pow; auto. }
      rewrite power_base_change with (b := b); lra.
    - apply sum_f_equiv; try lia.
      intros j H10. unfold n.
      rewrite floor_INR. 2 : { apply is_natural_pow; auto. }
      rewrite <- pow_div_sub; solve_R.
  Qed.

  Lemma lemma_4_3 :
    is_natural b ->
    let g := λ k, ∑ 0 (k - 1) (λ j, a ^ j * f (⌊b^(k-j)⌋)) in
    let p := log_ b a in
    ((∃ ε, ε > 0 /\ f = Ο(λ n, n ^^ (p - ε))) -> 
      g = Ο(λ k, (b^k) ^^ p)) /\
    (f = Θ(λ n, n ^^ p) -> 
      g = Θ(λ k, (b^k) ^^ p * k)) /\
    ((∃ c N, 0 < c < 1 /\ 
      (∀ n : ℕ, n >= N -> a * f (⌊n/b⌋) <= c * f n)) -> 
      g = Θ(λ k, f (⌊b^k⌋))).
  Proof.
    intros H0 g p. split; [| split].
    - intros [ε [H10 [c1 [N [H12 H13]]]]]. 
      set (q := b ^^ ε).
      assert (H14 : q > 1). { unfold q. apply Rpower_gt_1; try lra. }

      set (h := λ n : nat, n ^^ (p - ε)).

      assert (exists c2, ∀ n, (n >= 1)%nat -> |f n| <= c2 * |h n|) as [c2 H15].
      {
        apply big_o_extend_1 with (N := N) (c := c1); auto.
        intros n H15. unfold h. apply Rabs_pos_lt, Rgt_not_eq, Rpower_gt_0; solve_R.
      }

      pose proof floor_power_bound (p - ε) as [j [H16 H17]].

      set (c3 := Rmax 1 (c2 * j)).

      assert (H18 : c3 > 0). { unfold c3. solve_R. }
      
      exists (c3 * q / (q - 1)), 1. split; [apply Rdiv_pos_pos; nra |].
      intros n H19. unfold g. 
      rewrite Rabs_right.
      2 : {
        apply Rle_ge. apply sum_f_nonneg; try lia. intros k H20.
        specialize (H3 (⌊b^(n - k)⌋)). pose proof pow_lt a k ltac:(lra) as H21. nra.
      }

      apply Rle_trans with (r2 := ∑ 0 (n - 1) (λ k, a ^ k * (c3 * (b ^ (n - k)) ^^ (p - ε)))).
      {
        apply sum_f_congruence_le; try lia.
        intros k H20. 
        apply Rmult_le_compat_l; [apply pow_le; lra |].

        assert (H21 : (⌊b ^ (n - k)⌋ >= 1)%nat).
        {
          assert (H21 : b ^ (n - k) >= 1).
          { apply Rle_ge. apply pow_R1_Rle; lra. }
          pose proof floor_spec (b ^ (n - k)) ltac:(lra) as [H22 H23].
          destruct (⌊b ^ (n - k)⌋); simpl in *; solve_R.
        }

        specialize (H15 (⌊b^(n - k)⌋) H21). 
        rewrite Rabs_right in H15; auto.
        rewrite Rabs_right in H15; [ | apply Rpower_ge_0 ].
        apply Rle_trans with (c2 * h ⌊b ^ (n - k)⌋); auto.
        unfold h.
        assert (H22: 0 <= c2).
        { 
          apply Rmult_le_reg_r with (⌊b ^ (n - k)⌋ ^^ (p - ε)).
          - apply Rpower_gt_0. solve_R.
          - rewrite Rmult_0_l. apply Rle_trans with (f ⌊b ^ (n - k)⌋); auto.
            apply Rge_le. apply H3.
        }
        apply Rle_trans with (c2 * (j * (b ^ (n - k)) ^^ (p - ε))).
        + apply Rmult_le_compat_l; auto.
          apply H17. apply Rle_ge; apply pow_R1_Rle; lra.
        + rewrite <- Rmult_assoc.
          apply Rmult_le_compat_r.
          * apply Rge_le; apply Rpower_ge_0.
          * apply Rmax_r.
      }

      apply Rle_trans with (c3 * a ^ n * ∑ 0 (n - 1) (fun k => (1/q)^(n-k))).
      {
        replace (λ k : ℕ, a ^ k * (c3 * (b ^ (n - k))^^(p - ε))) with
                (λ k : ℕ, c3 * (a^k * (b ^ (n - k))^^(p - ε))) by (extensionality x; lra).
        rewrite <- r_mult_sum_f_i_n_f_l.
        right. rewrite Rmult_assoc. f_equal.
        rewrite r_mult_sum_f_i_n_f_l. 
        apply sum_f_equiv; [lia |].
        intros k H20.
        repeat rewrite <- Rpower_nat; try lra. 2 : { apply Rdiv_pos_pos; lra. }
        rewrite Rpower_mult; try lra.
        rewrite Rmult_minus_distr_l. unfold Rminus at 1. rewrite Rpower_plus; try lra.

        replace (b ^^ ((n - k)%nat * p)) with (a ^^ (n - k)).
        2: {
          rewrite Rmult_comm.
          rewrite <- Rpower_mult; [| lra]. unfold p.
          unfold log_. f_equal; [| rewrite minus_INR; solve_R]. unfold Rpower.
          destruct (Rlt_dec 0 b) as [H21 | H21]; try lra.
          replace (log a / log b * log b) with (log a).
          - rewrite exp_log; lra.
          - field. apply Rgt_not_eq. apply log_pos; lra.
        }
        rewrite <- Rmult_assoc.
        rewrite <- Rpower_plus; [| lra].
        replace (k + (n - k)) with (INR n) by lra.
        f_equal.
        unfold q.
        rewrite Rpower_inv; [| apply Rpower_gt_0; lra].
        rewrite Rpower_mult; [| lra].
        f_equal.
        lra.
      }

      replace (| (b ^ n) ^^ p |) with (a ^ n).
      2: { rewrite Rabs_right. apply power_base_change; try lra. apply Rpower_ge_0; lra. }
      rewrite Rmult_assoc. replace (c3 * q / (q - 1) * a ^ n) with (c3 * (a ^ n * (q / (q - 1)))) by nra.
      apply Rmult_le_compat_l; try lra. apply Rmult_le_compat_l. apply pow_le; lra.
      rewrite sum_f_geometric_rev.
      2 : { apply Rlt_not_eq. apply Rdiv_lt_1; lra. }
      2 : { apply INR_le. replace (INR 1) with 1 by auto. lra. }
      replace (q / (q - 1)) with (1 / (1 - 1 / q)).
      2: { field. split; lra. }
      apply Rmult_le_compat_r.
      + apply Rlt_le. apply Rinv_0_lt_compat. apply Rmult_lt_reg_r with (r := q); field_simplify; nra.
      + apply Rle_trans with (1 / q).
        * rewrite Rmult_minus_distr_l.
          rewrite Rmult_1_r.
          assert (0 <= 1 / q * (1 / q) ^ n).
          { apply Rmult_le_pos. pose proof Rdiv_pos_pos 1 q; lra. apply pow_le. pose proof Rdiv_pos_pos 1 q; lra. }
          lra.
        * apply Rlt_le. apply Rdiv_lt_1; lra.
    - intros [c1 [c2 [N [H8 [H9 H10]]]]].

      set (h := λ n : nat, n ^^ p).

      assert (exists c3, ∀ n, (n >= 1)%nat -> |f n| <= c3 * |h n|) as [c3 H11].
      {
        apply big_o_extend_1 with (N := N) (c := c2); [ | apply H10 ].
        intros n H11. unfold h. pose proof Rpower_gt_0 n p ltac:(solve_R); solve_R.
      }

      pose proof floor_power_bound p as [j [H12 H13]].
      pose proof floor_power_lower_bound p as [k [H14 H15]].
      { unfold p. apply log_b_nonneg; lra. }

      destruct (pow_unbounded b (Rmax (b * b) (N + 1)) H2) as [M H16].

      exists (c1 * k / 2), (Rmax c3 1 * j), (Rmax 1 (2 * M)).
      split; [solve_R | split]; [solve_R |]. intros n H17. split.
      + unfold g.
        rewrite Rabs_right. 2 : { pose proof Rpower_ge_0 (b ^ n) p as H18. solve_R. }
        rewrite Rabs_right. 2 : {
          apply Rle_ge. apply sum_f_nonneg; try lia. intros l H19.
          specialize (H3 (⌊b^(n - l)⌋)). pose proof pow_lt a l ltac:(lra) as H20. nra.
        }

        assert ((n - M < n - 1)%nat) as H18.
        {
          apply INR_lt. rewrite minus_INR. 2 : { apply INR_le. solve_R. }
          rewrite minus_INR. 2 : { apply INR_le. solve_R. }
          assert (M > 1) as H18.
          { replace (1) with (INR 1) by auto. apply lt_INR. destruct M; [ |destruct M]; solve_R. }
          solve_R.
        }
        rewrite sum_f_split with (j := (n - M)%nat); try lia.
        apply Rle_trans with (∑ 0 (n - M) (λ j0 : ℕ, a ^ j0 * f ⌊b ^ (n - j0)⌋)).
        2 : {
          rewrite <- Rplus_0_r at 1.
          apply Rplus_le_compat_l.
          apply sum_f_nonneg; try lia.
          intros j0 H19.
          apply Rmult_le_pos; [apply pow_le; lra | apply Rge_le; auto ].
        }
        apply Rle_trans with (∑ 0 (n - M) (λ j : ℕ, c1 * k * (b ^ n)^^p)).
        2 : {
          apply sum_f_congruence_le; try lia.
          intros j0 H19.
          
          assert (H20 : (⌊b ^ (n - j0)⌋ >= N)).
          {
            apply Rle_ge.

            assert (H20 : N + 1 <= b ^ (n - j0)).
            {
              apply Rle_trans with (b ^ M).
              - apply Rle_trans with (Rmax (b * b) (N + 1)); try lra; auto.
                solve_R.
              - apply Rle_pow; try lra. assert (M <= n)%nat as H21.
                { apply INR_le. solve_R. }
                lia.
            }
            apply Rle_trans with (b ^ (n - j0) - 1); try lra.
            assert (b ^ (n - j0) ≥ 0 ) as H21.
            { apply Rle_ge. apply pow_le; lra. }
            
            pose proof floor_spec (b ^ (n - j0)) H21 as H22. lra.
          }
          apply Rle_trans with (a ^ j0 * (c1 * k * (b ^ (n - j0)) ^^ p)).
          2 : {
            rewrite Rmult_assoc. apply Rmult_le_compat_l.
            - apply pow_le; lra.
            - rewrite Rmult_comm. apply Rle_trans with (c1 * ⌊b ^ (n - j0)⌋ ^^ p).
              2 : {
                specialize (H10 ⌊b ^ (n - j0)⌋ H20).
                rewrite Rabs_right in H10.
                rewrite Rabs_right in H10. lra.
                apply H3. apply Rpower_ge_0.
              }
              rewrite (Rmult_comm (k * _)).
              apply Rmult_le_compat_l; try lra.
              apply Rge_le, H15. apply Rle_ge; apply pow_R1_Rle; lra.
          }
          replace (a ^ j0 * (c1 * k * (b ^ (n - j0))^^p)) with (c1 * k * (a ^ j0 * (b ^ (n - j0))^^p)) by lra.
          apply Rmult_le_compat_l; try nra.
          unfold p. repeat rewrite <- power_base_change with (b := b); try lra.
          rewrite <- pow_add. replace (j0 + (n - j0))%nat with n; solve_R.
        }
        rewrite sum_f_const.
        replace (c1 * k / 2 * ((b ^ n)^^p * n)) with (c1 * k * (b ^ n)^^p * (n / 2)) by nra.
        apply Rmult_le_compat_l; try nra.
        * apply Rmult_le_pos; try nra. apply Rge_le. apply Rpower_ge_0.
        * assert (n / 2 <= n - M + 1) as H19 by solve_R.
          rewrite Nat.sub_0_r.
          rewrite plus_INR, minus_INR. simpl. lra. apply INR_le. solve_R.
      + unfold g.
        rewrite Rabs_right. 2 : {
          apply Rle_ge. apply sum_f_nonneg; try lia. intros l H19.
          specialize (H3 (⌊b^(n - l)⌋)). pose proof pow_lt a l ltac:(lra) as H20. nra.
        }
        rewrite Rabs_right. 2 : { pose proof Rpower_ge_0 (b ^ n) p as H18. solve_R. }

        assert (H18 : c3 >= 0).
        {
          specialize (H11 1%nat ltac:(lia)).
          rewrite Rabs_right in H11; [| apply H3 ].
          rewrite Rabs_right in H11; [| apply Rpower_ge_0].
          unfold h in H11. specialize (H3 1%nat). simpl in H11. rewrite Rpower_1_base in H11. lra.
        }

        apply Rle_trans with (∑ 0 (n - 1) (λ k0 : ℕ, c3 * j * (b ^ n)^^p)).
        2 : {
          rewrite sum_f_const. rewrite Nat.sub_0_r, Nat.sub_add. 2 : { apply INR_le. solve_R. }
          pose proof pos_INR n as H19.
          pose proof Rpower_ge_0 (b ^ n) p as H20.
          repeat rewrite Rmult_assoc.
          apply Rmult_le_compat_r; [ | solve_R ].
          apply Rmult_le_pos; try nra.
        }

        apply sum_f_congruence_le; try lia.
        intros k0 H19.

        assert (H20 : (⌊b ^ (n - k0)⌋ >= 1)%nat).
        {
          apply INR_le.
          assert ((n - k0) >= 1)%nat as H20.
          { assert (n >= 1)%nat as H20. { apply INR_le. solve_R. } lia. }
          assert (1 <= b ^ (n - k0)) as H21.
          { apply pow_R1_Rle; lra. }
          pose proof floor_spec (b ^ (n - k0)) ltac:(apply Rle_ge, pow_le; lra) as [H22 H23].
          simpl. destruct (⌊b ^ (n - k0)⌋). simpl in *. lra.
          rewrite S_INR. pose proof pos_INR n0; lra.
         }
        specialize (H11 _ H20).

        apply Rle_trans with (a ^ k0 * (c3 * ⌊b ^ (n - k0)⌋ ^^ p)).
        {
          apply Rmult_le_compat_l; [apply pow_le; lra |].
          rewrite Rabs_right in H11; [| apply H3].
          rewrite Rabs_right in H11; [| apply Rpower_ge_0].
          apply H11.
        }

        apply Rle_trans with (a ^ k0 * (c3 * (j * (b ^ (n - k0)) ^^ p))).
        {
          apply Rmult_le_compat_l; [apply pow_le; lra |].
          apply Rmult_le_compat_l; [apply Rge_le; apply H18 |].
          apply H13.
          apply Rle_ge, pow_R1_Rle; lra.
        }

        replace (a ^ k0 * (c3 * (j * (b ^ (n - k0)) ^^ p))) with (c3 * j * (a ^ k0 * (b ^ (n - k0)) ^^ p)) by lra.
        apply Rmult_le_compat_l; try nra.
        unfold p. repeat rewrite <- power_base_change with (b := b); try lra.
        rewrite <- pow_add. replace (k0 + (n - k0))%nat with n; solve_R.
      - intros [c [N [H10 H11]]].
    apply big_theta_iff; split.
    + destruct (pow_unbounded b (Rmax N b) H2) as [M H12].
      assert (H13 : (M > 0)%nat). { destruct M; [ | destruct M]; solve_R. }
      assert (H14: exists N' : nat, forall n : nat, (n >= N') -> 
      ∑ (S (n - M - 1)) (n - 1) (λ j : ℕ, a ^ j * f ⌊b ^ (n - j)⌋) <= f ⌊b ^ n⌋).
      {
        admit.
      }
      destruct H14 as [N' H14].
      exists (1 / (1 - c) + 1), (Rmax (Rmax N (INR M + 1)) (INR N')).
      split. { apply Rplus_lt_0_compat; [apply Rdiv_pos_pos; lra | lra]. }
      intros n H15.
      assert (H16: (n >= M + 1)%nat).
      { apply INR_ge. solve_R. }
      assert (H17: (n >= N')%nat).
      { apply INR_ge. solve_R. }
      rewrite Rabs_right.
      2: { apply Rle_ge. apply sum_f_nonneg; try lia. intros k H18.
           specialize (H3 (⌊b^(n - k)⌋)). pose proof pow_lt a k ltac:(lra) as H19. nra. }
      rewrite Rabs_right; [| apply H3].
      unfold g.
      rewrite (sum_f_split 0 (n - M - 1) (n - 1)); try lia.
      rewrite Rmult_plus_distr_r.
      apply Rplus_le_compat.
      * apply Rle_trans with (∑ 0 (n - M - 1) (fun j => c ^ j * f ⌊b ^ n⌋)).
        -- apply sum_f_congruence_le; try lia.
           intros j H18. apply iter_ineq_on_powers with (c2 := N) (M := M); auto; try lra.
        -- rewrite <- r_mult_sum_f_i_n_f, Rmult_comm. 
           apply Rmult_le_compat_r; [apply Rge_le, H3 |].
           replace (pow c) with (λ j : ℕ, c ^ j) by reflexivity.
           rewrite sum_f_geometric; try lra.
           apply Rmult_le_reg_r with (r := (1 - c)); [ lra |]. field_simplify; try lra.
           assert (H18 : c ^ (n - M - 1 + 1) >= 0). { apply Rle_ge, pow_le; lra. }
           lra.
      * rewrite Rmult_1_l. apply H14; solve_R.
    + exists 1, 2. split; [lra |].
      intros n H12. rewrite Rmult_1_l.
      rewrite Rabs_right.
      2: { apply Rle_ge; apply sum_f_nonneg; try lia; intros k H13.
           specialize (H3 (⌊b^(n - k)⌋)). pose proof pow_lt a k ltac:(lra); nra. }
      rewrite Rabs_right; [| apply H3].
      unfold g.
      rewrite (sum_f_split 0 0 (n - 1)).
      2 : { split; solve_R. replace 2 with (INR 2) in H12 by auto. apply INR_ge in H12. lia. }
      rewrite sum_f_0_0, pow_O, Nat.sub_0_r, Rmult_1_l.
      assert (H13 : ∑ 1 (n - 1) (λ j : ℕ, a ^ j * f ⌊b ^ (n - j)⌋) >= 0).
      { apply Rle_ge, sum_f_nonneg.
        { replace 2 with (INR 2) in H12 by auto. apply INR_ge in H12. lia. }
        intros k H14.
        apply Rmult_le_pos; [apply pow_le; lra | apply Rge_le; auto ]. }
      lra.
  Admitted.

  Lemma lemma_4_4 :
    let p := log_ b a in
    is_natural b ->
    ((∃ ε, ε > 0 /\ (f = Ο(λ n, n^^(p - ε)))) -> T' = Θ(λ k, (b^k)^^p)) /\
    (f = Θ(λ n, n^^p) -> T' = Θ(λ k, (b^k)^^p * k)) /\
    ((∃ ε c N, ε > 0 /\ 0 < c < 1 /\ (f = Ω(λ n, n^^(p + ε))) /\ 
     (∀ n : ℕ, n >= N -> a * f (⌊n/b⌋) <= c * f n)) -> T' = Θ(λ k, f (⌊b^k⌋))).
  Proof.
    intros p H8. 
    set (g := λ k, ∑ 0 (k - 1) (λ j, a ^ j * f (⌊b^(k-j)⌋))).
    pose proof lemma_4_3 H8 as [H9 [H10 H11]].
    fold g in H9, H10, H11.
    pose proof lemma_4_2 as H12.
    split; [| split].
    - intros [ε [H13 H14]]. specialize (H9 (ex_intro _ ε (conj H13 H14))). apply big_theta_iff; split.
      + apply big_o_trans with (λ k, (b ^ k) ^^ p + g k); [ | apply big_o_plus; auto; apply big_o_refl ].
        exists (Rmax 1 (T' 0)), 1%nat. split; [solve_R |]. intros n H15.
        specialize (H12 n ltac:(apply Rge_le, INR_le in H15; lia) H8).
        replace (∑ 0 (n - 1) λ j : ℕ, a ^ j * f ⌊b ^ (n - j)⌋) with (g n) in H12 by reflexivity.
        replace ((b ^ n) ^^ p) with (a ^ n).
        2 : { unfold p. rewrite power_base_change with (b := b); lra. }
        rewrite H12. pose proof pow_le a n ltac:(lra) as H16. rewrite H7, pow_O.
        replace 1 with (INR 1) by auto. rewrite floor_INR_id; auto.
        assert (H17 : 0 <= g n).
        { apply sum_f_nonneg; try lia. intros k H17. apply Rmult_le_pos; [apply pow_le; lra | apply Rge_le; auto ]. }
        solve_R.
      + exists (T 1), 1%nat. split; auto.
        intros n H15. specialize (H12 n ltac:(apply Rge_le, INR_le in H15; lia) H8).
        replace (∑ 0 (n - 1) λ j : ℕ, a ^ j * f ⌊b ^ (n - j)⌋) with (g n) in H12 by reflexivity.
        replace ((b ^ n) ^^ p) with (a ^ n).
        2 : { unfold p. rewrite power_base_change with (b := b); lra. }
        pose proof pow_le a n ltac:(lra) as H16.
        rewrite H12, H7, pow_O. replace 1 with (INR 1) by auto. rewrite floor_INR_id; auto.
        assert (H17 : 0 <= g n).
        { apply sum_f_nonneg; try lia. intros k H17. apply Rmult_le_pos; [apply pow_le; lra | apply Rge_le; auto ]. }
        solve_R.
    - intros H13. specialize (H10 H13). apply big_theta_iff; split.
      + apply big_o_trans with (λ k, (b ^ k) ^^ p + g k).
        * exists (Rmax 1 (T' 0)), 1%nat. split; [solve_R |]. intros n H14.
          specialize (H12 n ltac:(apply Rge_le, INR_le in H14; lia) H8).
          replace (∑ 0 (n - 1) λ j : ℕ, a ^ j * f ⌊b ^ (n - j)⌋) with (g n) in H12 by reflexivity.
          replace ((b ^ n) ^^ p) with (a ^ n).
          2 : { unfold p. rewrite power_base_change with (b := b); lra. }
          rewrite H12. pose proof pow_le a n ltac:(lra) as H15. rewrite H7, pow_O.
          replace 1 with (INR 1) by auto. rewrite floor_INR_id; auto.
          assert (H16 : 0 <= g n).
          { apply sum_f_nonneg; try lia. intros k H16. apply Rmult_le_pos; [apply pow_le; lra | apply Rge_le; auto ]. }
          solve_R.
        * apply big_o_plus; [ | apply big_theta_iff; auto ].
          exists 1, 1%nat. split; [solve_R |]. intros n H14. simpl in H14.
          pose proof Rpower_ge_0 (b ^ n) p as H15. solve_R.
      + apply big_omega_trans with g; [ | apply big_theta_iff; auto ].
        exists 1, 1%nat. split; [lra|]. intros n H14.
        specialize (H12 n ltac:(apply Rge_le, INR_le in H14; lia) H8).
        replace (∑ 0 (n - 1) λ j : ℕ, a ^ j * f ⌊b ^ (n - j)⌋) with (g n) in H12 by reflexivity.
        replace ((b ^ n) ^^ p) with (a ^ n).
        2 : { unfold p. rewrite power_base_change with (b := b); lra. }
        assert (H15 : 0 <= g n).
        { apply sum_f_nonneg; try lia. intros k H15. apply Rmult_le_pos; [apply pow_le; lra | apply Rge_le; auto ]. }
        rewrite H12. pose proof pow_le a n ltac:(lra) as H16. rewrite H7, pow_O.
        replace 1 with (INR 1) by auto. rewrite floor_INR_id; auto. simpl.
        solve_R.
    - intros [ε [c1 [c2 [H13 [H14 [H15 H16]]]]]].
      specialize (H11 (ex_intro _ c1 (ex_intro _ c2 (conj H14 H16)))).
      apply big_theta_iff; split.
      + apply big_o_trans with (λ k, (b ^ k) ^^ p + g k).
        * exists (Rmax 1 (T' 0)), 1%nat. split; [solve_R |]. intros n H17.
          specialize (H12 n ltac:(apply Rge_le, INR_le in H17; lia) H8).
          replace (∑ 0 (n - 1) λ j : ℕ, a ^ j * f ⌊b ^ (n - j)⌋) with (g n) in H12 by reflexivity.
          replace ((b ^ n) ^^ p) with (a ^ n).
          2 : { unfold p. rewrite power_base_change with (b := b); lra. }
          rewrite H12. pose proof pow_le a n ltac:(lra) as H18. rewrite H7, pow_O.
          replace 1 with (INR 1) by auto. rewrite floor_INR_id; auto.
          assert (H19 : 0 <= g n).
          { apply sum_f_nonneg; try lia. intros k H19. apply Rmult_le_pos; [apply pow_le; lra | apply Rge_le; auto ]. }
          solve_R.
        * apply big_o_plus; [ | apply big_theta_iff; auto ].
          destruct H15 as [c3 [N2 [H17 H18]]].
           apply big_o_trans with (λ k, (b ^ k) ^^ (p + ε)).
           { exists 1, 1%nat. split; [lra |]. intros n H19.
             rewrite Rmult_1_l. pose proof Rpower_exp_le (b^n) p (p + ε) ltac:(apply Rle_ge, pow_R1_Rle; lra) ltac:(lra) as H20.
             pose proof Rpower_ge_0 (b ^ n) p as H21. solve_R. }
           apply transpose_sym_O_Omega.
           destruct (pow_unbounded b (Rabs N2 + 2) H2) as [N3 HN3].
           exists (c3 / 2), (Rmax N3 (b * b)). split; [lra |]. intros n H19.
           pose proof pow_le b n ltac:(lra) as H20.
           specialize (H18 ⌊b ^ n⌋).
           assert (H21 : (⌊b ^ n⌋ >= N2)).
           { apply Rle_ge.
             rewrite floor_INR; [| apply is_natural_pow; auto].
             apply Rle_trans with (b ^ N3).
             - apply Rle_trans with (Rabs N2 + 2).
               + apply Rle_trans with (Rabs N2); [apply Rle_abs | lra].
               + apply Rge_le; auto.
             - apply Rle_pow; [lra |]. apply INR_le. solve_R.
           }
           specialize (H18 H21).
           apply Rle_ge.  apply Rmult_le_reg_r with 2; try lra. field_simplify.
           rewrite floor_INR in H18; [solve_R |]. apply is_natural_pow; auto.
      + apply big_omega_trans with g.
      * exists 1, 1%nat. split; [lra |]. intros n H17.
        specialize (H12 n ltac:(apply Rge_le, INR_le in H17; lia) H8).
        replace (∑ 0 (n - 1) λ j : ℕ, a ^ j * f ⌊b ^ (n - j)⌋) with (g n) in H12 by reflexivity.
        replace ((b ^ n) ^^ p) with (a ^ n).
        2 : { unfold p. rewrite power_base_change with (b := b); lra. }
        rewrite H12.
        assert (H18 : a ^ n * T' 0 >= 0).
        { pose proof pow_le a n ltac:(lra) as H19.
          rewrite H7, pow_O. replace 1 with (INR 1) by auto. rewrite floor_INR_id; auto. nra. }
        assert (H19 : 0 <= g n).
        { apply sum_f_nonneg; try lia. intros k H19. apply Rmult_le_pos; [apply pow_le; lra | apply Rge_le; auto ]. }
        rewrite Rmult_1_l. solve_R.
      * apply big_theta_iff in H11; destruct H11; auto.
  Qed.
End Master_Theorem.

Theorem master_theorem_nat : ∀ (a b : ℝ) (f T : ℕ -> ℝ),
  a >= 1 -> b > 1 -> is_natural b ->
  (∀ n, f n >= 0) ->
  (∀ n, T n >= 0) -> 
  (T 1%nat > 0) ->
  (∀ n : ℕ, n >= b -> T n = a * T (⌊n/b⌋) + f n) ->
  ((∃ ε, ε > 0 /\ (f = Ο(λ n, n^^((log_ b a) - ε)))) -> T = Θ(λ n, n^^(log_ b a))) /\
  (f = Θ(λ n, n^^(log_ b a)) -> T = Θ(λ n, n^^(log_ b a) * lg n)) /\
  ((∃ ε c N, ε > 0 /\ 0 < c < 1 /\ (f = Ω(λ n, n^^((log_ b a) + ε))) /\ 
   (∀ n : ℕ, n >= N -> a * f (⌊n/b⌋) <= c * f n)) -> T = Θ(f)).
Proof.
  intros a b f T H1 H2 H3 H4 H5 H6 H7.
  pose proof lemma_4_4 a b f T (λ n, T ⌊b ^ n⌋) H1 H2 H4 H5 H6 H7 as H8.
  specialize (H8 (λ k, eq_refl _) H3).
  set (p := log_ b a) in *.
  split; [| split].
  - intros H9. destruct H8 as [H10 _].
    specialize (H10 H9).
    apply big_theta_iff in H10. destruct H10 as [H11 H12].
    apply big_theta_iff. split.
    + admit.
    + admit.
  - intros H9. destruct H8 as [_ [H10 _]].
    specialize (H10 H9).
    apply big_theta_iff in H10. destruct H10 as [H11 H12].
    apply big_theta_iff. split.
    + admit.
    + admit.
  - intros H9. destruct H8 as [_ [_ H10]].
    specialize (H10 H9).
    apply big_theta_iff in H10. destruct H10 as [H11 H12].
    apply big_theta_iff. split.
    + admit.
    + admit.
Admitted.

Theorem master_theorem : ∀ (a b : ℝ) (f T : ℕ -> ℝ),
  a >= 1 -> b > 1 ->
  (∀ n, f n >= 0) ->
  (∀ n, T n >= 0) -> 
  (T 1%nat > 0) ->
  (∃ N, N >= b /\ (∀ n : ℕ, n >= N -> T n = a * T (⌊n/b⌋) + f n \/ T n = a * T (⌈n/b⌉) + f n)) ->
  ((∃ ε, ε > 0 /\ f = Ο(λ n, n^^((log_ b a) - ε))) -> T = Θ(λ n, n^^(log_ b a))) /\
  (∀ k, k > -1 -> f = Θ(λ n, n^^(log_ b a) * (lg n)^^k) -> T = Θ(λ n, n^^(log_ b a) * (lg n)^^(k + 1))) /\
  (f = Θ(λ n, n^^(log_ b a) * (lg n)^^(-1)) -> T = Θ(λ n, n^^(log_ b a) * lg (lg n))) /\
  (∀ k, k < -1 -> f = Θ(λ n, n^^(log_ b a) * (lg n)^^k) -> T = Θ(λ n, n^^(log_ b a))) /\
  ((∃ ε c N, ε > 0 /\ 0 < c < 1 /\ f = Ω(λ n, n^^((log_ b a) + ε)) /\ 
  (∀ n : ℕ, n >= N -> a * f (⌊n/b⌋) <= c * f n \/ a * f (⌈n/b⌉) <= c * f n)) -> T = Θ(f)).
Proof.
  intros a b f T H1 H2 H3 H4 H5 H6.
  split; [| split]; [ | | split; [| split ]].
  - intros [ε [H8 H9]]. admit.
  - intros k H8 H9. admit.
  - intros H8. admit.
  - intros k H8 H9. admit.
  - intros [ε [c [N [H8 [H9 [H10 H11]]]]]]. admit.
Admitted.

From Stdlib Require Recdef.

Module Problem2a.

Definition f (n : ℕ) := 7 * n^2 * lg (n^2).

Function T (n : nat) {measure (fun x => x) n} : R :=
  if le_dec n 2 then 1 
  else 
    4 * T (n / 2) + f n.
Proof.
  intros n H1 H2.
  apply Nat.div_lt; lia.
Defined.
  
Lemma H1 : ∀ n, f n ≥ 0.
Proof.
  intros n. unfold f. apply Rle_ge.
  pose proof pos_INR n as H1. 
  repeat apply Rmult_le_pos; try lra.
  - pose proof log_nonneg (n^2) as H2. admit.
  - (* Assuming lg n >= 0 for relevant n *) admit.
Admitted.

Lemma H2 : ∀ n, T n ≥ 0.
Proof.
  apply (well_founded_induction lt_wf); intros n IH.
  rewrite T_equation. pose proof H1 n as Hf.
  destruct (le_dec n 2); try lra.
  specialize (IH (n / 2)%nat ltac:(apply Nat.div_lt; lia)).
  lra.
Qed.

Lemma H3 : T 1 > 0.
Proof.
  compute; lra.
Qed.

Lemma H4 : ∃ N, N >= 2 /\ ∀ n : nat, n >= N → T n = 4 * T ⌊n / 2⌋ + f n.
Proof.
  exists 3. split; [lra |].
  intros n H1. replace (⌊n / 2⌋) with (n / 2)%nat.
  2 : { replace 2 with (INR 2%nat) by (simpl; lra). apply floor_div_general; lia. }
  rewrite T_equation.
  destruct (le_dec n 2); solve_R.
Qed.

Lemma problem_2a_solution : T = Θ(λ n, n^^2 * (lg n)^^2).
Proof.
  pose proof (master_theorem 4 2 f T ltac:(lra) ltac:(lra) H1 H2 H3) as [_ [_ [_ [_ H1]]]].
  destruct H4 as [N [H2 H3]]. exists N. auto.
  exists 2%R, 1%R, 1%R.
  repeat split; try lra.
  - admit.
  - admit.
Admitted.

End Problem2a.

Module Problem2b.

Definition f (n : ℕ) := 8 * n ^ 5.

Function T (n : nat) {measure (fun x => x) n} : R :=
  if le_dec n 2 then 42 
  else 
    5 * T (n / 7) + f n.
Proof.
  intros n H1 H2.
  apply Nat.div_lt; lia.
Defined.
  
Lemma H1 : ∀ n, f n ≥ 0.
Proof.
  intros n. unfold f. apply Rle_ge. apply Rmult_le_pos; try lra.
  apply pow_le. pose proof pos_INR n as H2. lra.
Qed.

Lemma H2 : ∀ n, T n ≥ 0.
Proof.
  apply (well_founded_induction lt_wf); intros n IH.
  rewrite T_equation. pose proof H1 n as H1.
  destruct (le_dec n 2) as [H2 | H2]; try lra.
  specialize (IH (n / 7)%nat ltac:(apply Nat.div_lt; lia)).
  lra.
Qed.

Lemma H3 : T 1 > 0.
Proof.
  compute; lra.
Qed.

Lemma H4 : ∃ N, N >= 7 /\ ∀ n : nat, n ≥ N → T n = 5 * T ⌊n / 7⌋ + f n.
Proof.
  exists 7. split; [lra |].
  intros n H1. replace (⌊n / 7⌋) with (n / 7)%nat.
  2 : { replace 7 with (INR 7%nat) by (simpl; lra). apply floor_div_general; lia. }
  rewrite T_equation.
  destruct (le_dec n 2); solve_R.
Qed.

Lemma problem_2b_solution : T = Θ(f).
Proof.
  pose proof (master_theorem 5 7 f T ltac:(lra) ltac:(lra) H1 H2 H3) as [_ [_ [_ [_ H1]]]].
  destruct H4 as [N [H2 H3]]. exists N. auto.
  apply H1.
  exists 1%R, (1/2)%R, 1%R.
  repeat split; try lra.
  - unfold f.
    admit.
  - intros n H8. 
    admit.
Admitted.

End Problem2b.

Section Examples.
  Let f1  := λ n : ℕ, 2.
  Let f2  := λ n : ℕ, 121!.
  Let f3  := λ n : ℕ, ln (19 * n ^ 4).
  Let f4  := λ n : ℕ, 7 * (ln (n ^ 3)) ^ 2.
  Let f5  := λ n : ℕ, 42 * n ^ (3/5).
  Let f6  := λ n : ℕ, n.
  Let f7  := λ n : ℕ, n * ln n.
  Let f8  := λ n : ℕ, log_ π (((2/23) * n) ^ (5 * n)).
  Let f9  := λ n : ℕ, n ^ 3 / (n ^ (1/2)).
  Let f10 := λ n : ℕ, (3/2) ^ n.
  Let f11 := λ n : ℕ, 2 ^ n.
  Let f12 := λ n : ℕ, (n!) ^ 2.

  Lemma f1_big_o_f2 : f1 = Ο(f2).
  Proof.
    unfold f1, f2. apply big_o_const_const; try lra.
    apply INR_fact_lt_0.
  Qed.

  Lemma f2_big_o_f3 : f2 = Ο(f3).
  Proof.
  Admitted.
  
End Examples.