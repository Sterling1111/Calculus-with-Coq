From Calculus.Chapter3 Require Export Prelude.
From Calculus.Chapter1 Require Import Problem_1_24.


Lemma lemma_3_16_a : forall (f : R -> R) l,
  (forall x y, f(x + y) = f x + f y) -> f(standard_sum l) = standard_sum (map f l).
Proof.
  intros f l.
  induction l as [|a l IHl].
  - intros H1. simpl. specialize (H1 0 0). rewrite Rplus_0_r in H1. nra.
  - intros H1. simpl. destruct l.
    -- simpl. reflexivity.
    -- simpl. rewrite H1. apply Rplus_eq_compat_l. simpl in IHl. apply IHl. apply H1.
Qed.