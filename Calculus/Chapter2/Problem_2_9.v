From Lib Require Import Imports WI_SI_WO.
Open Scope nat_scope.

Lemma lemma_2_9 : forall (A : nat -> Prop) (n0 : nat),
  (A n0 /\ (forall k : nat, A k -> A (S k))) ->
  forall n : nat, n >= n0 -> A n.
Proof.
  intros A n0 [H1 H2] n H3.
  induction n as [| k IH].
  - inversion H3. rewrite H in H1. apply H1.
  - assert (H4 : n0 = S k \/ n0 < S k) by lia. destruct H4 as [H4 | H4].
    -- rewrite H4 in H1. apply H1.
    -- apply H2. apply IH. lia.
Qed.