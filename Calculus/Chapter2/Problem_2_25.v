From Calculus.Chapter2 Require Import Prelude.

Definition Inductive (A : R -> Prop) : Prop :=
  A 1 /\ forall r : R, A r -> A (r + 1).

Definition Natural (r : R) : Prop :=
  forall A, Inductive A -> A r.

Lemma lemma_2_25_a_i : Inductive (fun r => True).
Proof.
  split; auto.
Qed.

Lemma lemma_2_25_a_ii : Inductive (fun r => r > 0).
Proof.
  split; intros; nra.
Qed.

Lemma lemma_2_25_a_iii : Inductive (fun r => r <> 1 / 2 /\ r > 0).
Proof.
  split; intros; nra.
Qed.

Lemma lemma_2_25_a_iv : ~Inductive (fun r => r > 0 /\ r <> 5).
Proof.
  intros [[H1 H2] H3]. specialize (H3 4). nra.
Qed.

Lemma lemma_2_25_a_v : forall (A B : R -> Prop),
  Inductive A /\ Inductive B -> Inductive (fun r => A r /\ B r).
Proof.
  intros A B [[H1 H2] [H3 H4]]. split.
  - auto.
  - intros r [H5 H6]. split; auto.
Qed.

Lemma lemma_2_25_b_i : Natural 1.
Proof.
  intros A [H1 H2]. auto.
Qed.

Lemma lemma_2_25_b_ii : forall k,
  Natural k -> Natural (k + 1).
Proof.
  intros k H1 A [H2 H3]. apply H3. apply H1. split; auto.
Qed.