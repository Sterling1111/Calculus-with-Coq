From Calculus.Chapter2 Require Import Prelude.

Lemma lemma_2_23_a : forall (a : R) (n m : nat),
  a ^ (n + m) = a^n * a^m.    
Proof.
  intros a n m. induction n as [| k IH].
  - simpl. lra.
  - replace (a ^ (S k + m)) with (a * (a ^ (k + m))) by (simpl; lra).
    rewrite IH. replace (a ^ S k) with (a * a ^ k) by (simpl; lra). lra.
Qed.

Lemma lemma_2_23_b : forall (a : R) (n m : nat),
  (a ^ n) ^ m = a ^ (n * m).
Proof.
  intros a n m. induction m as [| k IH].
  - simpl. rewrite Nat.mul_0_r. lra.
  - simpl. rewrite IH. rewrite <- lemma_2_23_a. 
    replace (n * S k)%nat with (n + n * k)%nat by lia. reflexivity.
Qed.