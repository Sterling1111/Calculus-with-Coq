From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_63_a : forall x y n,
  y <> 0 -> Nat.Even n -> x^n + y^n = (x + y)^n -> x = 0.
Proof.
  intros x y n H1 H2 H3.
  set (f := fun x => x^n + y^n - (x + y)^n).
  set (f' := fun x => n * x^(n - 1) - n * (x + y)^(n - 1)).

  assert (H4 : ⟦ der ⟧ f = f').
  { unfold f, f'; destruct n; [ | replace (S n - 1)%nat with n by lia]; auto_diff. }

  destruct (classic (x = 0)) as [H5 | H5]; auto.

  assert (f 0 = f x /\ f 0 = 0) as [H6 H7].
  {
    unfold f. destruct n; [lra |]. rewrite pow_i; try lia.
    rewrite H3. rewrite Rplus_0_l, Rplus_0_l. lra.
  }

  destruct (Rtotal_order x 0) as [H8 | [H8 | H8]]; auto.
  - assert (H9 : continuous_on f [x, 0]) by (unfold f; auto_cont).
    assert (H10 : differentiable_on f (x, 0)).
    {
      apply derivative_on_imp_differentiable_on with (f' := f').
      apply derivative_imp_derivative_on; auto. apply differentiable_domain_open; auto.
    }
    destruct (rolles_theorem f x 0 H8 H9 H10 ltac:(lra)) as [c H11].
    destruct H11 as [[H11 H12] H13].
    assert (H14 : f' c = 0) by exact (derivative_at_unique f f' (λ _ : ℝ, 0) c (H4 c) H13).
    destruct n as [ | n].
    + simpl in H3. lra.
    + unfold f' in H14. replace (S n - 1)%nat with n in H14 by lia.
      assert (H15 : INR (S n) ≠ 0) by (apply not_0_INR; lia).
      assert (H16 : c ^ n = (c + y) ^ n) by nra.
      assert (c = c + y) as H17.
      { apply pow_eq_odd in H16; auto. destruct H2 as [k H2]. exists (k - 1)%nat. lia. }
      nra.
  - assert (H9 : continuous_on f [0, x]) by (unfold f; auto_cont).
    assert (H10 : differentiable_on f (0, x)).
    {
      apply derivative_on_imp_differentiable_on with (f' := f').
      apply derivative_imp_derivative_on; auto. apply differentiable_domain_open; auto.
    }
    destruct (rolles_theorem f 0 x H8 H9 H10 ltac:(lra)) as [c H11].
    destruct H11 as [[H11 H12] H13].
    assert (H14 : f' c = 0) by exact (derivative_at_unique f f' (λ _ : ℝ, 0) c (H4 c) H13).
    destruct n as [ | n].
    + simpl in H3. lra.
    + unfold f' in H14. replace (S n - 1)%nat with n in H14 by lia.
      assert (H15 : INR (S n) ≠ 0) by (apply not_0_INR; lia).
      assert (H16 : c ^ n = (c + y) ^ n) by nra.
      assert (c = c + y) as H17.
      { apply pow_eq_odd in H16; auto. destruct H2 as [k H2]. exists (k - 1)%nat. lia. }
      nra.
Qed.

Lemma lemma_11_63_b : forall x y n,
  (n > 1)%nat -> y <> 0 -> Nat.Odd n -> x^n + y^n = (x + y)^n -> (x = 0 \/ x = -y).
Proof.
  intros x y n H0 H1 H2 H3.
  set (f := fun t => t^n + y^n - (t + y)^n).
  set (f' := fun t => INR n * t^(n - 1) - INR n * (t + y)^(n - 1)).

  assert (H4 : ⟦ der ⟧ f = f').
  { unfold f, f'. destruct n; [inversion H2 | replace (S n - 1)%nat with n by lia]; auto_diff. }

  destruct (classic (x = 0 \/ x = -y)) as [H5 | H5]; auto.
  exfalso. apply not_or_and in H5 as [H5 H6].

  assert (H7 : f 0 = 0).
  { unfold f. destruct n; [inversion H2; lia |]. rewrite pow_i; try lia. rewrite Rplus_0_l, Rplus_0_l. lra. }

  assert (H8 : f x = 0).
  { unfold f. lra. }

  assert (H9 : f (-y) = 0).
  { unfold f. replace (-y + y) with 0 by lra. destruct n; [inversion H2; lia |]. rewrite pow_i; try lia. rewrite pow_neg_odd; auto. lra. }

  assert (H10 : forall a b, a < b -> f a = 0 -> f b = 0 -> exists c, a < c < b /\ f' c = 0).
  { intros a b H10 H11 H12.
    assert (H13 : continuous_on f [a, b]) by (unfold f; auto_cont).
    assert (H14 : differentiable_on f (a, b)).
    { apply derivative_on_imp_differentiable_on with (f' := f').
      apply derivative_imp_derivative_on; auto. apply differentiable_domain_open; auto. }
    assert (H15 : f a = f b) by lra.
    destruct (rolles_theorem f a b H10 H13 H14 H15) as [c [H16 H17]].
    exists c. split; auto.
    exact (derivative_at_unique f f' (λ _ : ℝ, 0) c (H4 c) H17). }

  assert (H11 : exists c1 c2, c1 <> c2 /\ f' c1 = 0 /\ f' c2 = 0).
  {
    destruct (Rtotal_order 0 x) as [H12 | [H12 | H12]]; try lra;
    destruct (Rtotal_order 0 (-y)) as [H13 | [H13 | H13]]; try lra;
    destruct (Rtotal_order x (-y)) as [H14 | [H14 | H14]]; try lra.
    - destruct (H10 0 x H12 H7 H8) as [c1 [H15 H16]].
      destruct (H10 x (-y) H14 H8 H9) as [c2 [H17 H18]].
      exists c1, c2. repeat split; auto. lra.
    - destruct (H10 0 (-y) H13 H7 H9) as [c1 [H15 H16]].
      destruct (H10 (-y) x H14 H9 H8) as [c2 [H17 H18]].
      exists c1, c2. repeat split; auto. lra.
    - destruct (H10 (-y) 0 ltac:(lra) H9 H7) as [c1 [H15 H16]].
      destruct (H10 0 x H12 H7 H8) as [c2 [H17 H18]].
      exists c1, c2. repeat split; auto. lra.
    - destruct (H10 x 0 H12 H8 H7) as [c1 [H15 H16]].
      destruct (H10 0 (-y) H13 H7 H9) as [c2 [H17 H18]].
      exists c1, c2. repeat split; auto. lra.
    - destruct (H10 x (-y) H14 H8 H9) as [c1 [H15 H16]].
      destruct (H10 (-y) 0 H13 H9 H7) as [c2 [H17 H18]].
      exists c1, c2. repeat split; auto. lra.
    - destruct (H10 (-y) x H14 H9 H8) as [c1 [H15 H16]].
      destruct (H10 x 0 H12 H8 H7) as [c2 [H17 H18]].
      exists c1, c2. repeat split; auto. lra.
  }

  destruct H11 as [c1 [c2 [H11 [H12 H13]]]].

  assert (H14 : forall c, f' c = 0 -> c = -y / 2).
  { intros c H14. destruct n; [inversion H2; lia |].
    unfold f' in H14. replace (S n - 1)%nat with n in H14 by lia.
    assert (H15 : c ^ n = (c + y) ^ n).
    { apply Rmult_eq_reg_l with (r := INR (S n)); [lra | apply not_0_INR; lia]. }
    assert (H16 : c = c + y \/ c = -(c + y)).
    { apply pow_eq_even in H15; auto; try lia. destruct H2 as [k H16]. exists k. lia. }
    nra.
  }
  apply H14 in H12. apply H14 in H13. lra.
Qed.