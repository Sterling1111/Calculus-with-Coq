From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_7_a : forall f f',
  f = (fun x => x^3) ->
  ⟦ der ⟧ f = f' ->
  f' 9 = 243 /\ f' 25 = 1875 /\ f' 36 = 3888.
Proof.
  intros f f' H1 H2.
  assert (H3: ⟦ der ⟧ f = (fun x => 3 * x^2)).
  { subst. auto_diff. }
  rewrite (derivative_unique f f' (fun x => 3 * x^2) H2 H3).
  split; [| split]; simpl; lra.
Qed.

Lemma lemma_9_7_b : forall f f',
  f = (fun x => x^3) ->
  ⟦ der ⟧ f = f' ->
  f' (3^2) = 243 /\ f' (5^2) = 1875 /\ f' (6^2) = 3888.
Proof.
  intros f f' H1 H2.
  assert (H3: ⟦ der ⟧ f = (fun x => 3 * x^2)).
  { subst. auto_diff. }
  rewrite (derivative_unique f f' (fun x => 3 * x^2) H2 H3).
  split; [| split]; simpl; lra.
Qed.

Lemma lemma_9_7_c : forall f f' a x,
  f = (fun x => x^3) ->
  ⟦ der ⟧ f = f' ->
  f' (a^2) = 3 * a^4 /\ f' (x^2) = 3 * x^4.
Proof.
  intros f f' a x H1 H2.
  assert (H3: ⟦ der ⟧ f = (fun x => 3 * x^2)).
  { subst. auto_diff. }
  rewrite (derivative_unique f f' (fun x => 3 * x^2) H2 H3).
  split; simpl; lra.
Qed.

Lemma lemma_9_7_d : forall f f' g g',
  f = (fun x => x^3) ->
  ⟦ der ⟧ f = f' ->
  g = (fun x => f (x^2)) ->
  ⟦ der ⟧ g = g' ->
  forall x, g' x = 2 * x * f' (x^2).
Proof.
  intros f f' g g' H1 H2 H3 H4 x.
  assert (H5: ⟦ der ⟧ f = (fun x => 3 * x^2)).
  { subst. auto_diff. }
  assert (H6: f' = (fun x => 3 * x^2)).
  { apply (derivative_unique f f' (fun x => 3 * x^2) H2 H5). }
  assert (H7: ⟦ der ⟧ g = (fun x => 6 * x^5)).
  { subst. auto_diff. }
  rewrite (derivative_unique g g' (fun x => 6 * x^5) H4 H7).
  rewrite H6.
  simpl; lra.
Qed.
