From Lib Require Import Imports Sets Reals_util Notations Functions Interval Complex Limit.
Import SetNotations IntervalNotations FunctionNotations LimitNotations.

Open Scope C_scope.
Open Scope R_scope.

Definition limit_c (f : C -> C) (a L : C) :=
  forall ε, ε > 0 ->
    exists δ, δ > 0 /\
      forall z : C, 0 < |z - a|%C < δ -> |f z - L|%C < ε.

Module C_LimitNotations.

  Declare Scope C_limit_scope.
  Delimit Scope C_limit_scope with Clim.

  Notation "⟦ 'lim' a ⟧ f '=' L" := 
    (limit_c f a L) 
      (at level 70, f at level 0, no associativity, format "⟦  'lim'  a  ⟧  f  '='  L") : C_limit_scope.

  Open Scope C_limit_scope.
      
End C_LimitNotations.

Import C_LimitNotations.

Theorem limit_c_component_iff_clean : forall (f : C -> C) (a l : C),
  let u := fun z => fst (f z) in
  let v := fun z => snd (f z) in
  let α := fst l in
  let β := snd l in
  ⟦ lim a ⟧ f = l <->
  (⟦ lim a ⟧ u = α /\ ⟦ lim a ⟧ v = β).
Proof.
  intros f a l u v α β. split.
  - intros H1. split; intros ε H2.
    + specialize (H1 ε H2) as [δ [H3 H4]].
      exists δ. split; auto. intros x H5.
      unfold u, α. 
      specialize (H4 x H5). apply Rle_lt_trans with (r2 := (|(f x - l)|)%C); auto.
      assert (H6 : (|(fst (f x) - fst l)|)%C = Rabs (fst ((f x - l)%C))).
      { unfold Cminus, Copp, Cplus, Cnorm, Cnorm2. simpl.
        rewrite <- (sqrt_Rsqr_abs (fst (f x) + - fst l)).
        f_equal. unfold Rsqr. ring. }
      rewrite H6. apply Cnorm_fst.
    + specialize (H1 ε H2) as [δ [H3 H4]].
      exists δ. split; auto. intros x H5.
      unfold v, β. 
      specialize (H4 x H5). apply Rle_lt_trans with (r2 := (|(f x - l)|)%C); auto.
      assert (H6 : (|(snd (f x) - snd l)|)%C = Rabs (snd ((f x - l)%C))).
      { unfold Cminus, Copp, Cplus, Cnorm, Cnorm2. simpl.
        rewrite <- (sqrt_Rsqr_abs (snd (f x) + - snd l)).
        f_equal. unfold Rsqr. ring. }
      rewrite H6. apply Cnorm_snd.
  - intros [H1 H2] ε H3. 
    specialize (H1 (ε/2)%R ltac:(lra)) as [δ1 [H4 H5]].
    specialize (H2 (ε/2)%R ltac:(lra)) as [δ2 [H6 H7]].
    set (δ := Rmin δ1 δ2). exists δ. split; [ solve_R |].
    intros z H8. 
    assert (H9 : 0 < (|(z - a)|)%C < δ1) by (unfold δ in *; solve_min; lra).
    assert (H10 : 0 < (|(z - a)|)%C < δ2) by (unfold δ in *; solve_min; lra).
    specialize (H5 z H9).
    specialize (H7 z H10).
    apply Rle_lt_trans with (r2 := (|u z - α| + |v z - β|)%R).
    + assert (H11 : (|u z - α|)%R = Rabs (fst ((f z - l)%C))).
      { unfold u, α, Cminus, Copp, Cplus; simpl. reflexivity. }
      assert (H12 : (|v z - β|)%R = Rabs (snd ((f z - l)%C))).
      { unfold v, β, Cminus, Copp, Cplus; simpl. reflexivity. }
      rewrite H11, H12. apply Cnorm_le_sum_abs.
    + assert (H11 : (|(u z - α)|)%C = (|u z - α|)%R).
      { unfold Cminus, Copp, Cplus, Cnorm, Cnorm2; simpl. rewrite <- (sqrt_Rsqr_abs (u z - α)). f_equal. unfold Rsqr, u, α. ring. }
      assert (H12 : (|(v z - β)|)%C = (|v z - β|)%R).
      { unfold Cminus, Copp, Cplus, Cnorm, Cnorm2; simpl. rewrite <- (sqrt_Rsqr_abs (v z - β)). f_equal. unfold Rsqr, v, β. ring. }
      rewrite H11 in H5. rewrite H12 in H7. lra.
Qed.
