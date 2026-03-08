From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_26_i : forall f f' f'' x,
  f = (fun x => x^3) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ f' = f'' -> f'' x = 6 * x.
Proof.
Admitted.

Lemma lemma_9_26_ii : forall f f' f'' x,
  f = (fun x => x^5) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ f' = f'' -> f'' x = 20 * x^3.
Proof.
Admitted.

Lemma lemma_9_26_iii : forall f f' f'' x,
  ⟦ der ⟧ f = (fun y => y^4) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ f' = f'' -> f'' x = 4 * x^3.
Proof.
Admitted.

Lemma lemma_9_26_iv : forall f f' f'' x,
  f = (fun x => (x + 3)^5) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ f' = f'' -> f'' x = 20 * (x + 3)^3.
Proof.
Admitted.
