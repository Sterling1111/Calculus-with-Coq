From Calculus.Chapter2 Require Import Prelude Problem_2_12.
Open Scope R_scope.

Lemma lemma_2_15_a : forall x p q m,
  rational p -> rational q -> x = p + sqrt q -> q >= 0 ->
    exists a b, rational a /\ rational b /\ x^m = a + b * sqrt q.
Proof.
  intros x p q m H1 H2 H3 H4. induction m as [| m' IH].
  - exists 1, 0. repeat split.
    -- exists 1%Z, 1%Z. lra.
    -- exists 0%Z, 1%Z. lra.
    -- lra.
  - destruct IH as [a [b [H5 [H6 H7]]]]. exists (p * a + q * b), (p * b + a); repeat split.
    -- apply lemma_2_12_a; apply mult_rational; auto.
    -- apply lemma_2_12_a; try apply mult_rational; auto.
    -- simpl. rewrite H7. rewrite H3. replace ((p + sqrt q) * (a + b * sqrt q)) with (p * a + p * b * sqrt q + sqrt q * a + b * (sqrt q * sqrt q)) by nra.
       rewrite sqrt_sqrt; lra. 
Qed.

Lemma lemma_2_15_b : forall p q m,
  rational p -> rational q -> q >= 0 ->
    exists a b, rational a /\ rational b /\ (p - sqrt q)^m = a - b * sqrt q.
Proof.
  intros p q m H1 H2 H3. induction m as [| m' IH].
  - exists 1, 0. repeat split.
    -- exists 1%Z, 1%Z. lra.
    -- exists 0%Z, 1%Z. lra.
    -- lra.
  - destruct IH as [a [b [H4 [H5 H6]]]]. exists (p * a + q * b), (p * b + a); repeat split.
    -- apply lemma_2_12_a; apply mult_rational; auto.
    -- apply lemma_2_12_a; try apply mult_rational; auto.
    --  simpl. rewrite H6. replace ((p - sqrt q) * (a - b * sqrt q)) with (p * a - p * b * sqrt q - sqrt q * a + b * (sqrt q * sqrt q)) by nra.
       rewrite sqrt_sqrt; lra.
Qed.