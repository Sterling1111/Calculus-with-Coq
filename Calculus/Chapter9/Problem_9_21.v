From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_21_a : ∀ f a L,
  ⟦ der a ⟧ f = (λ _, L) <-> ⟦ lim a ⟧ (λ x, (f x - f a) / (x - a)) = L.
Proof.
  intros f a L.
  split; intros H1.
  - apply limit_eq with (f1 := λ x, (λ h, (f (a + h) - f a) / h) (x - a)).
    + exists 1. split; [lra |]. intros x H2.
      replace (a + (x - a)) with x by lra. reflexivity.
    + apply limit_comp with (f := λ h, (f (a + h) - f a) / h) (g := λ x, x - a) (b := 0); try auto_limit.
      exists 1. split; try lra. intros x H2. solve_R.
  - apply limit_eq with (f1 := λ h, (λ x, (f x - f a) / (x - a)) (a + h)).
    + exists 1. split; try lra. intros h H2.
      replace (a + h - a) with h by lra. reflexivity.
    + apply limit_comp with (f := λ x, (f x - f a) / (x - a)) (g := λ h, a + h) (b := a); try auto_limit.
      exists 1. split; try lra. intros h H2. solve_R.
Qed.

Lemma lemma_9_21_a' : ∀ f a L,
  ⟦ der a ⟧ f = (λ _, L) <-> ⟦ lim a ⟧ (λ x, (f x - f a) / (x - a)) = L.
Proof.
  intros f a L. split; intros H1.
  - unfold derivative_at in H1. replace a with (0 + a) at 1 by lra.
    rewrite <- limit_shift with (a := 0) (c := a).
    replace ((λ x : ℝ, (f (x + a) - f a) / (x + a - a))) with (λ x, (f (a + x) - f a) / x); auto.
    extensionality x. replace (x + a - a) with x by lra. rewrite Rplus_comm. reflexivity.
  - unfold derivative_at. replace a with (0 + a) in H1 at 1 by lra.
    rewrite <- limit_shift with (a := 0) (c := a) in H1.
    replace ((λ x : ℝ, (f (x + a) - f a) / (x + a - a))) with (λ x, (f (a + x) - f a) / x) in H1; auto.
    extensionality x. replace (x + a - a) with x by lra. rewrite Rplus_comm. reflexivity.
Qed.

Lemma lemma_9_21_a'' : ∀ f a L,
  ⟦ der a ⟧ f = (λ _, L) <-> ⟦ lim a ⟧ (λ x, (f x - f a) / (x - a)) = L.
Proof.
  intros f a L.
  unfold derivative_at.
  replace a with (0 + a) by lra.
  rewrite <- limit_shift with (a := 0) (c := a).
  repeat replace (0 + a) with a by lra.
  replace (λ x, (f (x + a) - f a) / (x + a - a)) with (λ h, (f (a + h) - f a) / h); try reflexivity.
  extensionality h. replace (h + a - a) with h by lra. rewrite Rplus_comm. reflexivity.
Qed.

Lemma lemma_9_21_b : ∀ f g a l,
  (∃ δ, δ > 0 /\ ∀ x, |x - a| < δ -> f x = g x) ->
  ⟦ der a ⟧ f = (fun _ => l) ->
  ⟦ der a ⟧ g = (fun _ => l).
Proof.
  intros f g a l [δ [H1 H2]] H3. 
  apply limit_eq with (f1 := λ h, (f (a + h) - f a) / h); auto.
  exists δ. split; auto. intros h H4; auto.
  repeat rewrite H2; solve_R.
Qed.