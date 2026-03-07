From Calculus.Chapter5 Require Import Prelude.

Section Problem_5_6.
  Variable f g : R -> R.
  Hypothesis H1 : forall ε x, ε > 0 -> 0 < |x - 2| < (sin (ε^2 / 9))^2 + ε -> |f x - 2| < ε.
  Hypothesis H2 : forall ε x, ε > 0 -> 0 < |x - 2| < ε^2 -> |g x - 4| < ε.

  Lemma lemma_5_6_i : ⟦ lim 2 ⟧ (fun x => f x + g x) = 6. 
  Proof.
    assert (H3 : ⟦ lim 2 ⟧ f = 2).
    { 
      unfold limit. intros ε H3. exists ((sin (ε ^ 2 / 9)) ^ 2 + ε).
      split; auto. pose proof (pow2_ge_0 (sin (ε ^ 2 / 9))); lra.
    }
    assert (H4 : ⟦ lim 2 ⟧ g = 4).
    { unfold limit. intros ε H4. exists (ε^2). split; auto; nra. }
    replace 6 with (2 + 4) by lra.
    apply limit_plus; auto.
  Qed.

  Lemma lemma_5_6_ii : ⟦ lim 2 ⟧ (fun x => f x * g x) = 8. 
  Proof.
    assert (H3 : ⟦ lim 2 ⟧ f = 2).
    { 
      unfold limit. intros ε H3. exists ((sin (ε ^ 2 / 9)) ^ 2 + ε).
      split; auto. pose proof (pow2_ge_0 (sin (ε ^ 2 / 9))); lra.
    }
    assert (H4 : ⟦ lim 2 ⟧ g = 4).
    { unfold limit. intros ε H4. exists (ε^2). split; auto; nra. }
    replace 8 with (2 * 4) by lra.
    apply limit_mult; auto.
  Qed.

  Lemma lemma_5_6_iii : ⟦ lim 2 ⟧ (fun x => 1 / g x) = 1/4.
  Proof.
    assert (H3 : ⟦ lim 2 ⟧ g = 4).
    { unfold limit. intros ε H3. exists (ε^2). split; auto; nra. }
    replace (1 / 4) with (/ 4) by lra; apply limit_inv; auto; lra.
  Qed.

  Lemma lemma_5_6_iv : ⟦ lim 2 ⟧ (fun x => f x / g x) = 1/2. 
  Proof.
    assert (H3 : ⟦ lim 2 ⟧ f = 2).
    { 
      unfold limit. intros ε H3. exists ((sin (ε ^ 2 / 9)) ^ 2 + ε).
      split; auto. pose proof (pow2_ge_0 (sin (ε ^ 2 / 9))); lra.
    }
    assert (H4 : ⟦ lim 2 ⟧ g = 4).
    { unfold limit. intros ε H4. exists (ε^2). split; auto; nra. }
    replace (1/2) with (2/4) by lra; apply limit_div; auto; lra.
  Qed.

End Problem_5_6.