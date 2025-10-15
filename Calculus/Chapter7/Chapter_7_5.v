From Lib Require Import Imports Sets Limit Continuity Rational Notations Reals_util.
Import LimitNotations IntervalNotations SetNotations.
Open Scope R_scope.

Lemma lemma_7_5 : ∀ f a b,
  a < b -> continuous_on f [a, b] -> (∀ x, rational (f x)) -> ∃ c, ∀ x, x ∈ [a, b] -> f x = c.
Proof.
  intros f a b H1 H2 H3. pose proof Rtotal_order (f a) (f b) as [H4 | [H4 | H4]].
  - pose proof exists_irrational_between (f a) (f b) H4 as [c [H5 H6]].
    pose proof theorem_7_4 f a b c H1 H2 H5 as [x [H7 H8]]. specialize (H3 x).
    subst. unfold irrational in H6. contradiction.
  - pose proof classic (∃ c : ℝ, ∀ x : ℝ, x ∈ [a, b] -> f x = c) as [H5 | H5]; auto.
    assert (H6 : ∀ c, ∃ x, x ∈ [a, b] /\ f x ≠ c).
    {
      intros c. apply not_all_not_ex. intros H6. apply H5. exists c.
      intros x H7. specialize (H6 x). apply not_and_or in H6 as [H6 | H6]; tauto.
    }
    clear H5. specialize (H6 (f a)) as [x [H5 H7]].
    assert (f x < f a \/ f x > f a) as [H8 | H8] by lra.
    -- pose proof exists_irrational_between (f x) (f a) H8 as [c [H9 H10]].
       assert (H12 : a < x). { pose proof Rtotal_order a x as [H11 | [H11 | H11]]; subst; solve_R. }
       assert (H13 : continuous_on f [a, x]). { apply continuous_on_subset with (A2 := [a, b]); auto. intros y. solve_R. }
       pose proof theorem_7_5 f a x c H12 H13 H9 as [d [H14 H15]]. specialize (H3 d).
       subst. unfold irrational in H10. contradiction.
    -- pose proof exists_irrational_between (f a) (f x) H8 as [c [H9 H10]].
       assert (H12 : a < x). { pose proof Rtotal_order a x as [H11 | [H11 | H11]]; subst; solve_R. }
       assert (H13 : continuous_on f [a, x]). { apply continuous_on_subset with (A2 := [a, b]); auto. intros y. solve_R. }
       pose proof theorem_7_4 f a x c H12 H13 H9 as [d [H14 H15]]. specialize (H3 d).
       subst. unfold irrational in H10. contradiction.
  - pose proof exists_irrational_between (f b) (f a) H4 as [c [H5 H6]].
    pose proof theorem_7_5 f a b c H1 H2 H5 as [x [H7 H8]]. specialize (H3 x).
    subst. unfold irrational in H6. contradiction.  
Qed.