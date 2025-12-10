From Calculus.Chapter5 Require Import Prelude.

Lemma lemma_5_9 : ∀ f a L,
  ⟦ lim a ⟧ f = L <->  ⟦ lim 0 ⟧ (λ h, f(a + h)) = L.
Proof.
  intros f a L. split; intros H1 ε H2.
  - specialize (H1 ε H2). destruct H1 as [δ [H1 H3]].
    exists δ. split; auto. intros h H4.
    specialize (H3 (a + h) ltac:(solve_R)). solve_R.
  - specialize (H1 ε H2). destruct H1 as [δ [H1 H3]].
    exists δ. split; auto. intros h H4.
    specialize (H3 (h - a) ltac:(solve_R)).
    replace (a + (h - a)) with h in H3 by lra. solve_R.
Qed.