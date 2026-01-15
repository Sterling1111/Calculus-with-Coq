From Calculus.Chapter9 Require Import Prelude.

Lemma problem_9_24 : ∀ f a L,
  odd_f f -> 
  (⟦ der a ⟧ f = (λ _, L) <-> ⟦ der -a ⟧ f = (λ _, L)).
Proof.
  intros f a L H1.
  split; intros H2.
  - apply limit_eq with (f1 := λ x, (f (a + (-x)) - f a) / (-x)).
    + exists 1. split; try lra. intros x H3.
      rewrite (H1 a). replace (-a + x) with (- (a - x)) by lra.
      rewrite (H1 (a - x)). replace (a + -x) with (a - x) by lra.
      replace (- f (a - x) - - f a) with (- (f (a - x) - f a)) by lra.
      solve_R.
    + apply limit_comp with (f := λ x, (f (a + x) - f a) / x) (g := λ x, -x) (b := 0); try auto_limit.
      exists 1. split; try lra. intros x H3. solve_R.
  - apply limit_eq with (f1 := λ x, (f (-a + (-x)) - f (-a)) / (-x)).
    + exists 1. split; try lra. intros x H3.
      rewrite (H1 a). replace (a + x) with (- (-a - x)) by lra.
      rewrite (H1 (-a - x)). replace (-a + -x) with (-a - x) by lra.
      replace (- f (-a - x) - - f (-a)) with (- (f (-a - x) - f (-a))) by lra.
      solve_R.
    + apply limit_comp with (f := λ x, (f (-a + x) - f (-a)) / x) (g := λ x, -x) (b := 0); try auto_limit.
      exists 1. split; try lra. intros x H3. solve_R.
Qed.
