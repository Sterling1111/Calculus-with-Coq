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