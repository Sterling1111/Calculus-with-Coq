From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_41_a : 
  let f := (λ x, x^2 - cos x) in
  exists x1 x2, x1 <> x2 /\ 
  f x1 = 0 /\ f x2 = 0 /\
  (forall x, f x = 0 -> x = x1 \/ x = x2).
Proof.
  intros f.

  set (f' := λ y, 2 * y + sin y).
  set (f'' := λ y, 2 + cos y).

  assert (H1 : f 0 < 0).
  { unfold f. simpl. rewrite Rmult_0_l, Rminus_0_l, cos_0. lra. }
  assert (H2 : f 1 > 0).
  { unfold f. simpl. pose proof cos_1_bounds as H2. lra. }
  assert (H3 : f (-1) > 0).
  {
    unfold f. simpl. replace (-1) with (-(1)) by lra.
    pose proof cos_1_bounds as H3. rewrite cos_even_odd. lra.
  }

  assert (exists x1, -1 < x1 < 0 /\ f x1 = 0) as [x1 [H4 H5]].
  {
    pose proof (intermediate_value_theorem_decreasing f (-1) 0 0 ltac:(lra)) ltac:(unfold f; auto_cont) ltac:(lra) as [x [H6 H7]].
    exists x. split; auto.
    assert (x = -1 \/ x = 0 \/ x ∈ (-1, 0)) as [H8 | [H8 | H8]]; subst; solve_R.
  }

  assert (exists x2, 0 < x2 < 1 /\ f x2 = 0) as [x2 [H6 H7]].
  {
    pose proof (intermediate_value_theorem f 0 1 0 ltac:(lra)) ltac:(unfold f; auto_cont) ltac:(lra) as [x [H8 H9]].
    exists x. split; auto.
    assert (x = 0 \/ x = 1 \/ x ∈ (0, 1)) as [H10 | [H10 | H10]]; subst; solve_R.
  }
  
  exists x1, x2; repeat split; try solve [solve_R].
  intros x H8.
  
  assert (H9 : ⟦ der ⟧ f = f') by (unfold f, f'; auto_diff).
  assert (H10 : ⟦ der ⟧ f' = f'') by (unfold f', f''; auto_diff).
  
  destruct (classic (x = x1 \/ x = x2)) as [H11 | H11]; auto.
  apply not_or_and in H11 as [H12 H13].

  assert (H14 : forall a b, a < b -> f a = 0 -> f b = 0 -> exists c, a < c < b /\ 2 * c + sin c = 0).
  {
    intros a b H15 H16 H17.
    assert (H18 : continuous_on f [a, b]) by (unfold f; auto_cont).
    assert (H19 : differentiable_on f (a, b)).
    {
      apply derivative_on_imp_differentiable_on with (f' := fun y => 2 * y + sin y).
      apply derivative_imp_derivative_on; auto.
      apply differentiable_domain_open; lra.
    }
    assert (H20 : f a = f b) by lra.
    pose proof (rolles_theorem f a b H15 H18 H19 H20) as [c [H21 H22]].
    exists c. split; [exact H21 |].
    pose proof (derivative_at_unique f (λ _, 0) (fun y => 2 * y + sin y) c H22 (H9 c)) as H23; auto.
  }
  
  assert (H15 : forall a b, a < b -> 2 * a + sin a = 0 -> 2 * b + sin b = 0 -> exists c, a < c < b /\ 2 + cos c = 0).
  {
    intros a b H16 H17 H18.
    assert (H19 : continuous_on (fun y => 2 * y + sin y) [a, b]) by auto_cont.
    assert (H20 : differentiable_on (fun y => 2 * y + sin y) (a, b)).
    {
      apply derivative_on_imp_differentiable_on with (f' := fun y => 2 + cos y).
      apply derivative_imp_derivative_on; auto.
      apply differentiable_domain_open; lra.
    }
    assert (H21 : 2 * a + sin a = 2 * b + sin b) by lra.
    pose proof (rolles_theorem (fun y => 2 * y + sin y) a b H16 H19 H20 H21) as [c [H22 H23]].
    exists c. split; [exact H22 |].
    pose proof (derivative_at_unique (fun y => 2 * y + sin y) (λ _, 0) (fun y => 2 + cos y) c H23 (H10 c)) as H24; auto.
  }
  
  assert (exists c, 2 + cos c = 0) as [c H16].
  {
    assert (x < x1 \/ x1 < x < x2 \/ x2 < x) as [H17 | [H17 | H17]] by lra.
    - pose proof (H14 x x1 H17 H8 H5) as [c1 [H18 H19]].
      pose proof (H14 x1 x2 ltac:(lra) H5 H7) as [c2 [H20 H21]].
      pose proof (H15 c1 c2 ltac:(lra) H19 H21) as [c [H22 H23]].
      exists c; exact H23.
    - pose proof (H14 x1 x ltac:(lra) H5 H8) as [c1 [H18 H19]].
      pose proof (H14 x x2 ltac:(lra) H8 H7) as [c2 [H20 H21]].
      pose proof (H15 c1 c2 ltac:(lra) H19 H21) as [c [H22 H23]].
      exists c; exact H23.
    - pose proof (H14 x1 x2 ltac:(lra) H5 H7) as [c1 [H18 H19]].
      pose proof (H14 x2 x ltac:(lra) H7 H8) as [c2 [H20 H21]].
      pose proof (H15 c1 c2 ltac:(lra) H19 H21) as [c [H22 H23]].
      exists c; exact H23.
  }
  
  pose proof (cos_bounds c) as H18.
  lra.
Qed.