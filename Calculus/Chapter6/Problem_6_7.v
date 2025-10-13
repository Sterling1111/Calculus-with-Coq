From Lib Require Import Imports Notations Limit Continuity Reals_util.
Import LimitNotations.
Open Scope R_scope.

Lemma lemma_6_7 : forall f,
  (forall x y, f(x + y) = f(x) + f(y)) -> 
  continuous_at f 0 -> forall a, continuous_at f a.
Proof.
  intros f H1 H2 a ε H3.
  specialize (H2 ε H3) as [δ [H4 H5]].
  exists δ. split; auto.
  intros x H6.
  assert (H7 : f 0 = 0).
  { specialize (H1 0 0). simpl in H1. rewrite Rplus_0_l in H1. lra. }
  assert (H8 : f x - f a = f (x - a)).
  { specialize (H1 a (x - a)). replace (a + (x - a)) with x in H1 by lra. lra. }
  specialize (H5 (x - a) ltac:(solve_R)). rewrite H7, <- H8 in H5.
  rewrite Rminus_0_r in H5. auto.
Qed.