From Calculus.Chapter12 Require Import Prelude.

Lemma lemma_12_24_a : forall f, 
  continuous f -> inverse f f -> exists x, f x = x.
Proof.
  intros f H1 H2.
  unfold inverse in H2. destruct H2 as [H3 [H4 [H5 H6]]].
  destruct (Rlt_dec (f 0) 0) as [H7 | H7].
  - destruct (intermediate_value_theorem_decreasing (fun x => f x - x) (f 0) 0 0) as [x [H8 H9]].
    + auto.
    + auto_cont.
    + split.
      * replace (f 0 - 0) with (f 0) by lra. exact H7.
      * replace (f (f 0) - f 0) with (0 - f 0). 2: { rewrite H5; auto. apply Full_intro. } lra.
    + exists x. lra.
  - destruct (Req_dec (f 0) 0) as [H8 | H8].
    + exists 0. auto.
    + destruct (intermediate_value_theorem_decreasing (fun x => f x - x) 0 (f 0) 0) as [x [H9 H10]].
      * lra.
      * auto_cont.
      * split.
        -- replace (f (f 0) - f 0) with (0 - f 0). 2: { rewrite H5; auto. apply Full_intro. } lra.
        -- replace (f 0 - 0) with (f 0) by lra. lra.
      * exists x. lra.
Qed.

Lemma lemma_12_24_c : forall f,
  increasing f ->
  inverse f f ->
  forall x, f x = x.
Admitted.