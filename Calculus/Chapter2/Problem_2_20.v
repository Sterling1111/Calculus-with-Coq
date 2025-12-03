From Calculus.Chapter2 Require Export Prelude.

Local Notation F := fibonacci_R'.

Lemma lemma_2_20 : forall n,
  F n = (((1 + √5)/2)^n - ((1 - √5)/2)^n) / √5.
Proof.
  intros n. strong_induction n. destruct n as [| n'].
  - simpl. lra.
  - assert (H1 : 0 < √5) by (apply sqrt_lt_R0; lra). destruct n' as [| n''].
    -- simpl. field. lra.
    -- replace (F (S (S n''))) with (F (S n'') + F n'') by auto.
       rewrite IH. 2 : { lia. } rewrite IH. 2 : { lia. } apply Rmult_eq_reg_r with (r := √5). 2 : { lra. }
       replace (((((1 + √5) / 2) ^ S n'' - ((1 - √5) / 2) ^ S n'') / √5 + (((1 + √5) / 2) ^ n'' - ((1 - √5) / 2) ^ n'') / √5) * √5)
       with (((((1 + √5) / 2) ^ S n'' - ((1 - √5) / 2) ^ S n'') + (((1 + √5) / 2) ^ n'' - ((1 - √5) / 2) ^ n''))) by (field; lra).
       replace ((((1 + √5) / 2) ^ S (S n'') - ((1 - √5) / 2) ^ S (S n'')) / √5 * √5)
       with ((((1 + √5) / 2) ^ S (S n'') - ((1 - √5) / 2) ^ S (S n''))) by (field; lra).
       replace (((1 + √5) / 2) ^ S n'' - ((1 - √5) / 2) ^ S n'' + (((1 + √5) / 2) ^ n'' - ((1 - √5) / 2) ^ n''))
       with (((1 + √5) / 2)^ S n'' + ((1 + √5) / 2) ^ n'' - ((1 - √5) / 2) ^ S n'' - ((1 - √5) / 2) ^ n'') by lra.
       replace (((1 + √5) / 2) ^ S n'' + ((1 + √5) / 2) ^ n'') with (((1 + √5) / 2) ^ n'' * (1 + ((1 + √5) / 2))) by (simpl; lra).
       replace (((1 + √5) / 2) ^ n'' * (1 + (1 + √5) / 2) - ((1 - √5) / 2) ^ S n'' - ((1 - √5) / 2) ^ n'') with
       (((1 + √5) / 2) ^ n'' * (1 + (1 + √5) / 2) - (1 - √5) / 2 * ((1 - √5) / 2) ^ n'' - ((1 - √5) / 2) ^ n'') by (simpl; lra).
       replace (((1 + √5) / 2) ^ n'' * (1 + (1 + √5) / 2) - (1 - √5) / 2 * ((1 - √5) / 2) ^ n'' - ((1 - √5) / 2) ^ n'') with
       (((1 + √5) / 2) ^ n'' * (1 + (1 + √5) / 2) - ((1 - √5) / 2) ^ n'' * (1 + ((1 - √5) / 2))) by (simpl; lra).
       replace (1 + ((1 - √5) / 2)) with (((1 - √5) / 2)^2).
       2 : { replace (((1 - √5) / 2)^2) with ((1 - 2 * √5 + √5 * √5) / 4). 2 : { simpl. field. } rewrite sqrt_sqrt. 2 : { lra. } field. }
       replace (1 + (1 + √5) / 2) with (((1 + √5) / 2)^2).
       2 : { replace (((1 + √5) / 2)^2) with ((1 + 2 * √5 + √5 * √5) / 4). 2 : { simpl. field. } rewrite sqrt_sqrt. 2 : { lra. } field. }
       replace (((1 + √5) / 2) ^ n'' * ((1 + √5) / 2) ^ 2) with (((1 + √5) / 2) ^ (S (S n''))). 2 : { simpl. field. }
       replace (((1 - √5) / 2) ^ n'' * ((1 - √5) / 2) ^ 2) with (((1 - √5) / 2) ^ (S (S n''))). 2 : { simpl. field. }
       field.
Qed.