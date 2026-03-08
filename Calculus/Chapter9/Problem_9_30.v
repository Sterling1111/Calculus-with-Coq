From Calculus.Chapter9 Require Import Prelude.

Lemma lemma_9_30_i : forall n f f' x,
  f = (fun x => x^n) -> ⟦ der ⟧ f = f' -> f' x = INR n * x^(n - 1).
Proof.
Admitted.

Lemma lemma_9_30_ii : forall f f' y,
  f = (fun y => 1 / y) -> ⟦ der ⟧ f = f' -> f' y = -1 / y^2.
Proof.
Admitted.

Lemma lemma_9_30_iii : forall f f' g g' c x,
  g = (fun x => f x + c) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> g' x = f' x.
Proof.
Admitted.

Lemma lemma_9_30_iv : forall f f' g g' c x,
  g = (fun x => c * f x) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> g' x = c * f' x.
Proof.
Admitted.

Lemma lemma_9_30_v : forall f f' g g' y c,
  g = (fun x => f x + c) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> g' y = f' y.
Proof.
Admitted.

Lemma lemma_9_30_vi : forall f f' a,
  f = (fun x => x^3) -> ⟦ der ⟧ f = f' -> f' (a^2) = 3 * a^4.
Proof.
Admitted.

Lemma lemma_9_30_vii : forall f f' g g' a b,
  g = (fun x => f (x + a)) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> g' b = f' (b + a).
Proof.
Admitted.

Lemma lemma_9_30_viii : forall f f' g g' c b,
  g = (fun x => f (c * x)) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> g' b = c * f' (c * b).
Proof.
Admitted.

Lemma lemma_9_30_ix : forall f f' g g' c x,
  g = (fun y => f (c * y)) -> ⟦ der ⟧ f = f' -> ⟦ der ⟧ g = g' -> g' x = c * f' (c * x).
Proof.
Admitted.

Lemma lemma_9_30_x : forall n k f x,
  (k <= n)%nat -> 
  f = (fun x => x^n) -> ⟦ Der ^ k x ⟧ f = INR (fact n) / INR (fact (n - k)) * x^(n - k).
Proof.
Admitted.
