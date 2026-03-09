From Calculus.Chapter11 Require Import Prelude.

Lemma lemma_11_34_b : forall f f' L1 L2,
  ⟦ lim ∞ ⟧ f = L1 ->
  ⟦ lim ∞ ⟧ f' = L2 ->
  (exists M, forall x, x > M -> ⟦ der x ⟧ f = f') ->
  L2 = 0.
Admitted.

Lemma lemma_11_34_c : forall f f'' L1 L2,
  ⟦ lim ∞ ⟧ f = L1 ->
  ⟦ lim ∞ ⟧ f'' = L2 ->
  (exists M, forall x, x > M -> ⟦ der ^ 2 x ⟧ f = (fun _ => f'' x)) ->
  L2 = 0.
Admitted.
