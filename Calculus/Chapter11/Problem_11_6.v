From Calculus.Chapter11 Require Import Prelude.

Lemma left_endpoint_lt_interior : forall f a b z,
  a < b ->
  z ∈ (a, b) ->
  continuous_on f [a, b] ->
  increasing_on f (a, b) ->
  f a < f z.
Proof.
  intros f a b z H1 H2 H3 H4.
  assert (f a < f z \/ f a >= f z) as [H5 | H5] by lra; auto.
  exfalso.
  set (w := (a + z) / 2).
  assert (w ∈ (a, z)) as H6 by (unfold w; solve_R).
  assert (f w < f z) as H7. { apply H4; solve_R. }
  assert (f w < f a) as H8 by lra.
  set (v := (f w + f a) / 2).
  assert (f w < v < f a) as H9 by (unfold v; lra).
  assert (a < w) as H10 by solve_R.
  assert (continuous_on f [a, w]) as H11.
  { apply continuous_on_subset with (A2 := [a, b]); auto. intros x' y'; solve_R. }
  destruct (intermediate_value_theorem_decreasing f a w v H10 H11 H9) as [u [H12 H13]].
  assert (u <> w) as H14 by (intro H14; subst u; lra).
  assert (a <> u) as H15 by (intro H15; subst u; lra).
  assert (a < u /\ u < w) as H16 by solve_R.
  assert (f u < f w) as H17. { apply H4; solve_R. }
  lra.
Qed.

Lemma interior_lt_right_endpoint : forall f a b z,
  a < b ->
  z ∈ (a, b) ->
  continuous_on f [a, b] ->
  increasing_on f (a, b) ->
  f z < f b.
Proof.
  intros f a b z H1 H2 H3 H4.
  destruct (Rle_lt_dec (f b) (f z)) as [H5 | H5]; auto.
  exfalso.
  set (w := (z + b) / 2).
  assert (w ∈ (z, b)) as H6 by (unfold w; solve_R).
  assert (f z < f w) as H7. { apply H4; solve_R. }
  assert (f b < f w) as H8 by lra.
  set (v := (f w + f b) / 2).
  assert (f b < v < f w) as H9 by (unfold v; lra).
  assert (w < b) as H10 by solve_R.
  assert (continuous_on f [w, b]) as H11.
  { apply continuous_on_subset with (A2 := [a, b]); auto. intros x' y'; solve_R. }
  destruct (intermediate_value_theorem_decreasing f w b v H10 H11 H9) as [u [H12 H13]].
  assert (u <> w) as H14 by (intro H14; subst u; lra).
  assert (b <> u) as H15 by (intro H15; subst u; lra).
  assert (w < u /\ u < b) as H16 by solve_R.
  assert (f w < f u) as H17. { apply H4; solve_R. }
  lra.
Qed.

Lemma lemma_11_6 : forall f a b,
  a < b ->
  continuous_on f [a, b] ->
  increasing_on f (a, b) ->
  increasing_on f [a, b].
Proof.
  intros f a b H1 H2 H3 x y H4 H5 H6.
  assert (
    (x ∈ (a, b) /\ y ∈ (a, b)) \/
    (x = a      /\ y ∈ (a, b)) \/
    (x ∈ (a, b) /\ y = b)      \/
    (x = a      /\ y = b)
  ) as [[H7 H8] | [[H7 H8] | [[H7 H8] | [H7 H8]]]] by solve_R; subst.
  - apply H3; auto.
  - apply (left_endpoint_lt_interior f a b y H1 H8 H2 H3).
  - apply (interior_lt_right_endpoint f a b x H1 H7 H2 H3).
  - set (z := (a + b) / 2).
    assert (z ∈ (a, b)) as H9 by (unfold z; solve_R).
    assert (f a < f z) as H10 by (apply (left_endpoint_lt_interior f a b z H1 H9 H2 H3)).
    assert (f z < f b) as H11 by (apply (interior_lt_right_endpoint f a b z H1 H9 H2 H3)).
    lra.
Qed.