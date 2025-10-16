From Lib Require Import Imports Sets Limit Continuity Rational Notations Reals_util.
Import LimitNotations IntervalNotations SetNotations.
Open Scope R_scope.

Lemma lemma_7_5 : ∀ f a b,
  a < b -> continuous_on f [a, b] -> (∀ x, rational (f x)) -> ∃ c, ∀ x, x ∈ [a, b] -> f x = c.
Proof.
  intros f a b H1 H2 H3. pose proof classic (∃ c : ℝ, ∀ x : ℝ, x ∈ [a, b] → f x = c) as [H4 | H4]; auto.
  assert (H5 : ∀ c, ∃ x, x ∈ [a, b] /\ f x ≠ c).
  {
    intros c. apply not_all_not_ex. intros H5. apply H4. exists c.
    intros x H6. specialize (H5 x). apply not_and_or in H5 as [H5 | H5]; tauto.
  }
  clear H4. specialize (H5 (f a)) as [x [H4 H5]].
  assert (f x < f a \/ f x > f a) as [H6 | H6] by lra.
  - pose proof exists_irrational_between (f x) (f a) H6 as [c [H7 H8]].
    assert (H10 : a < x). { pose proof Rtotal_order a x as [H9 | [H9 | H9]]; subst; solve_R. }
    assert (H11 : continuous_on f [a, x]). { apply continuous_on_subset with (A2 := [a, b]); auto. intros y. solve_R. }
    pose proof theorem_7_5 f a x c H10 H11 H7 as [d [H12 H13]]. specialize (H3 d).
    subst. unfold irrational in H8. contradiction.
  - pose proof exists_irrational_between (f a) (f x) H6 as [c [H7 H8]].
    assert (H10 : a < x). { pose proof Rtotal_order a x as [H9 | [H9 | H9]]; subst; solve_R. }
    assert (H11 : continuous_on f [a, x]). { apply continuous_on_subset with (A2 := [a, b]); auto. intros y. solve_R. }
    pose proof theorem_7_4 f a x c H10 H11 H7 as [d [H12 H13]]. specialize (H3 d).
    subst. unfold irrational in H8. contradiction.
Qed.