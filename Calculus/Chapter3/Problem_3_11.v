From Calculus.Chapter3 Require Export Prelude.

Parameter H : ℝ -> ℝ.
Parameter y : ℝ.

Axiom H1 : H (H y) = y.

Fixpoint iter {A : Type} (n : nat) (f : A -> A) (x : A) : A :=
  match n with
  | O => x
  | S n' => iter n' f (f x)
  end.

Lemma iter_succ {A : Type} (n : nat) (f : A -> A) (x : A) :
  iter (S n) f x = iter n f (f x).
Proof.
  reflexivity.
Qed.

Lemma lemma_13_11_a : iter 80 H y = y.
Proof.
  compute; repeat rewrite H1; reflexivity.
Qed.

Lemma lemma_13_11_b : iter 81 H y = H y.
Proof.
  rewrite iter_succ.
Qed.