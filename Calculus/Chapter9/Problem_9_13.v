From Calculus.Chapter9 Require Import Prelude.
Open Scope R_scope.

Lemma lemma_9_13 : forall f f' g g' h a,
  f a = g a ->
  ⟦ der a⁻ ⟧ f = f' ->
  ⟦ der a⁺ ⟧ g = g' ->
  f' a = g' a ->
  (forall x, x <= a -> h x = f x) ->
  (forall x, x >= a -> h x = g x) ->
  differentiable_at h a.
Proof.
  intros f f' g g' h a H1 H2 H3 H4 H5 H6.
  exists (f' a). intros ε H7.
  specialize (H2 ε H7) as [δ1 [H8 H9]].
  specialize (H3 ε H7) as [δ2 [H10 H11]].
  set (δ := Rmin δ1 δ2).
  exists δ. split; [ unfold δ; solve_R | ].
  intros x H12. destruct (Rtotal_order x 0) as [H13 | [H13 | H13]]; try solve [ solve_R ].
  - rewrite (H5 (a + x) ltac:(unfold δ in *; solve_R)), (H5 a ltac:(solve_R)).
    specialize (H9 x ltac:(unfold δ in *; solve_R)). solve_R.
  - rewrite (H6 (a + x) ltac:(unfold δ in *; solve_R)), (H6 a ltac:(solve_R)).
    specialize (H11 x ltac:(unfold δ in *; solve_R)). solve_R. 
Qed.