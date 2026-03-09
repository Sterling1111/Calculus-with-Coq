From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_62 : forall f a,
  continuous_at f a ->
  differentiable_at (fun x => |f x|) a ->
  differentiable_at f a.
Admitted.
