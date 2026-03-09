From Calculus.Chapter10 Require Import Prelude.

Lemma lemma_10_22_a : forall (l : list R),
  exists (g : R -> R), ⟦ der ⟧ g = (fun x => polynomial l x).
Proof.
Admitted.

Lemma lemma_10_22_b : forall (m : nat) (b : nat -> R),
  (m >= 2)%nat ->
  exists (g : R -> R), forall x, x <> 0 -> 
    ⟦ Der x ⟧ g = ∑ 2 m (fun k => b k / x^k).
Proof.
Admitted.

Lemma lemma_10_22_c : ~ exists (n m : nat) (a b : nat -> R),
  forall x, x <> 0 ->
    ⟦ Der x ⟧ (fun t => ∑ 0 n (fun k => a k * t^k) + ∑ 1 m (fun k => b k / t^k)) = 1 / x.
Proof.
Admitted.