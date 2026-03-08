From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_13_a : forall f a b,
  a < b -> continuous_on f [a, b] -> exists g,
    (forall x, x ∈ [a, b] -> g x = f x) /\ continuous_on g ℝ.
Proof.
  intros f a b H1 H2.
  set (g := fun x => if Rle_dec x a then f a else if Rle_dec x b then f x else f b).
  exists g. split.
  - intros x H3. unfold g. destruct (Rle_dec x a) as [H4 | H4]; destruct (Rle_dec x b) as [H5 | H5]; try solve_R. 
    replace x with a by solve_R. reflexivity.
  - unfold continuous_on in *. intros x _ ε H3.
    assert (x < a \/ x ∈ [a, b] \/ x > b) as [H4 | [H4 | H4]] by solve_R.
    + exists (a - x). split; [solve_R |].
      intros y _ H5. unfold g.
      destruct (Rle_dec x a) as [H6 | H6]; destruct (Rle_dec y a) as [H7 | H7]; solve_R.
    + specialize (H2 x H4 ε H3). destruct H2 as [δ [H5 H6]].
      exists δ. split; [solve_R |].
      intros y _ H7.
      assert (x = a \/ a < x < b \/ x = b) as [H8 | [H8 | H8]] by solve_R.
      * subst x. assert (g a = f a) as H9. { unfold g. destruct (Rle_dec a a); destruct (Rle_dec a b); solve_R. }
        rewrite H9. assert (y <= a \/ a < y <= b \/ y > b) as [H10 | [H10 | H10]] by solve_R.
        -- assert (g y = f a) as H11. { unfold g. destruct (Rle_dec y a); solve_R. }
           rewrite H11. solve_R.
        -- assert (g y = f y) as H11. { unfold g. destruct (Rle_dec y a); destruct (Rle_dec y b); solve_R. }
           rewrite H11. assert (0 < |y - a| < δ) as H12 by solve_R. specialize (H6 y ltac:(solve_R) H12). solve_R.
        -- assert (g y = f b) as H11. { unfold g. destruct (Rle_dec y a); destruct (Rle_dec y b); solve_R. }
           rewrite H11. assert (0 < |b - a| < δ) as H12 by solve_R. specialize (H6 b ltac:(solve_R) H12). solve_R.
      * assert (g x = f x) as H9. { unfold g. destruct (Rle_dec x a); destruct (Rle_dec x b); solve_R. }
        rewrite H9. assert (y <= a \/ a < y <= b \/ y > b) as [H10 | [H10 | H10]] by solve_R.
        -- assert (g y = f a) as H11. { unfold g. destruct (Rle_dec y a); solve_R. }
           rewrite H11. assert (0 < |a - x| < δ) as H12 by solve_R. specialize (H6 a ltac:(solve_R) H12). solve_R.
        -- assert (g y = f y) as H11. { unfold g. destruct (Rle_dec y a); destruct (Rle_dec y b); solve_R. }
           rewrite H11. assert (x = y \/ x <> y) as [H12 | H12] by lra.
           ++ subst y. solve_R.
           ++ assert (0 < |y - x| < δ) as H13 by solve_R. specialize (H6 y ltac:(solve_R) H13). solve_R.
        -- assert (g y = f b) as H11. { unfold g. destruct (Rle_dec y a); destruct (Rle_dec y b); solve_R. }
           rewrite H11. assert (0 < |b - x| < δ) as H12 by solve_R. specialize (H6 b ltac:(solve_R) H12). solve_R.
      * subst x. assert (g b = f b) as H9. { unfold g. destruct (Rle_dec b a); destruct (Rle_dec b b); solve_R. }
        rewrite H9. assert (y <= a \/ a < y <= b \/ y > b) as [H10 | [H10 | H10]] by solve_R.
        -- assert (g y = f a) as H11. { unfold g. destruct (Rle_dec y a); solve_R. }
           rewrite H11. assert (0 < |a - b| < δ) as H12 by solve_R. specialize (H6 a ltac:(solve_R) H12). solve_R.
        -- assert (g y = f y) as H11. { unfold g. destruct (Rle_dec y a); destruct (Rle_dec y b); solve_R. }
           rewrite H11. assert (0 < |y - b| < δ) as H12 by solve_R. specialize (H6 y ltac:(solve_R) H12). solve_R.
        -- assert (g y = f b) as H11. { unfold g. destruct (Rle_dec y a); destruct (Rle_dec y b); solve_R. }
           rewrite H11. solve_R.
    + exists (x - b). split; [solve_R |].
      intros y _ H5. unfold g.
      destruct (Rle_dec x b) as [H6 | H6]; destruct (Rle_dec y b) as [H7 | H7]; solve_R.
Qed.