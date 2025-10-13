From Lib Require Import Imports.
Open Scope nat_scope.

Lemma lemma_2_8 : forall n : nat,
  Nat.Even n \/ Nat.Odd n.
Proof.
  intros n. induction n as [| k IH].
  - left. unfold Nat.Even. exists 0. lia.
  - destruct IH as [IH | IH].
    -- right. unfold Nat.Odd in *. destruct IH as [k0 H]. exists (k0). lia.
    -- left. unfold Nat.Even in *. destruct IH as [k0 H]. exists (S k0). lia.
Qed.

Lemma lemma_2_8' : forall z : Z,
  Z.Even z \/ Z.Odd z.
Proof.
  intros z. rewrite <- Zeven_equiv. rewrite <- Zodd_equiv.
  destruct (Zeven_odd_dec z) as [H | H].
  - auto.
  - auto.
Qed.