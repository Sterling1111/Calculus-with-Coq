From Calculus.Chapter3 Require Export Prelude.

Lemma lemma_3_17_a : forall f : R -> R, 
  (forall x y, f (x + y) = f x + f y) -> 
  (forall x y, f (x * y) = f x * f y) -> 
  (exists x, f x <> 0) -> f 1 = 1.
Proof.
Admitted.

Lemma lemma_3_17_b : forall f : R -> R, 
  (forall x y, f (x + y) = f x + f y) -> 
  (forall x y, f (x * y) = f x * f y) -> 
  (exists x, f x <> 0) -> forall x, rational x -> f x = x.
Proof.
Admitted.

Lemma lemma_3_17_c : forall f : R -> R, 
  (forall x y, f (x + y) = f x + f y) -> 
  (forall x y, f (x * y) = f x * f y) -> 
  (exists x, f x <> 0) -> forall x, x > 0 -> f x > 0.
Proof.
Admitted.

Lemma lemma_3_17_d : forall f : R -> R, 
  (forall x y, f (x + y) = f x + f y) -> 
  (forall x y, f (x * y) = f x * f y) -> 
  (exists x, f x <> 0) -> forall x y, x > y -> f x > f y.
Proof.
Admitted.

Lemma lemma_3_17_e : forall f : R -> R, 
  (forall x y, f (x + y) = f x + f y) -> 
  (forall x y, f (x * y) = f x * f y) -> 
  (exists x, f x <> 0) -> forall x, f x = x.
Proof.
Admitted.
