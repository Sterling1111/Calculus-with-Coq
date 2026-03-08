From Calculus.Chapter2 Require Import Prelude.

Open Scope nat_scope.

Lemma lemma_2_24_a : forall a b c,
  a * (b + c) = a * b + a * c.
Proof.
  intros a b c. induction a as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. lia.
Qed.

Lemma lemma_2_24_b : forall a,
  a * 1 = a.
Proof.
  intros a. induction a as [| k IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

Lemma lemma_2_24_c : forall a b,
  a * b = b * a.
Proof.
  intros a b. induction b as [| k IH].
  - simpl. rewrite Nat.mul_0_r. reflexivity.
  - simpl. rewrite <- IH. rewrite <- lemma_2_24_b with (a := a) at 2. rewrite <- lemma_2_24_a.
    simpl. reflexivity.
Qed.