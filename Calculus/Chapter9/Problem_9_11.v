From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_11_a : forall s s' k,
  ⟦ der ⟧ s = s' -> (forall t, s' t = k * s t) -> ~ (exists c, c <> 0 /\ forall t, s t = c * t^2).
Proof.
Admitted.

Lemma lemma_9_11_b_i : forall s s' s'' a,
  s = (fun t => (a / 2) * t^2) -> ⟦ der ⟧ s = s' -> ⟦ der ⟧ s' = s'' -> forall t, s'' t = a.
Proof.
Admitted.

Lemma lemma_9_11_b_ii : forall s s' a,
  s = (fun t => (a / 2) * t^2) -> ⟦ der ⟧ s = s' -> forall t, (s' t)^2 = 2 * a * s t.
Proof.
Admitted.
