From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_5 : ∀ a f f',
  a <> 0 -> f = (λ x, |x|) -> ⟦ der a ⟧ f = f' -> f' a = a / |a|.