From Calculus.Chapter7 Require Import Prelude.

Lemma lemma_7_11 : forall f,
  continuous_on f [0, 1] ->
  (forall x, x ∈ [0, 1] -> f x ∈ [0, 1]) ->
  exists x, x ∈ [0, 1] /\ f x = x.
Proof.
  intros f H1 H2.
  destruct (Req_dec (f 0) 0) as [H3|H3]; [exists 0; split; solve_R|].
  destruct (Req_dec (f 1) 1) as [H4|H4]; [exists 1; split; solve_R|].
  set (h := fun x => x - f x).
  assert (H5 : continuous_on h [0, 1]).
  { unfold h. intros x H5. apply limit_on_minus; auto. apply limit_on_id. }
  assert (h 0 < 0 < h 1) as H6.
  {
    unfold h. specialize (H2 0 ltac:(solve_R)) as H6.
    specialize (H2 1 ltac:(solve_R)). solve_R.
  }
  pose proof intermediate_value_theorem h 0 1 0 ltac:(solve_R) H5 H6 as [x [H7 H8]].
  exists x; split; auto; unfold h in *; solve_R.
Qed.