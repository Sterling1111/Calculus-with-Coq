From Calculus.Chapter6 Require Import Prelude.

Lemma lemma_6_6_a :
  exists f, (forall x, (exists n : nat, (n > 0)%nat /\ x = 1 / INR n) -> ~ continuous_at f x) /\
            (forall x, ~ (exists n : nat, (n > 0)%nat /\ x = 1 / INR n) -> continuous_at f x).
Proof. Admitted.

Lemma lemma_6_6_b :
  exists f, ~(continuous_at f 0) /\ (forall x, (exists n : nat, (n > 0)%nat /\ x = 1 / INR n) -> ~ continuous_at f x) /\
            (forall x, x <> 0 -> ~ (exists n : nat, (n > 0)%nat /\ x = 1 / INR n) -> continuous_at f x).
Proof. Admitted.
