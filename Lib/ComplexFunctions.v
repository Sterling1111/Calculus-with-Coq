From Lib Require Import Imports Sets Notations Functions Sums Complex Limit Trigonometry Exponential Sequence Series Reals_util
                        ComplexLimit ComplexContinuity ComplexDerivative ComplexSequence ComplexSeries.
Import SetNotations FunctionNotations LimitNotations SequenceNotations SumNotations SeriesNotations.

Open Scope C_scope.
Open Scope R_scope.

Definition Cpolar (r θ : R) : C :=
  (r * cos θ, r * sin θ).

Lemma Cpolar_mult : forall r1 θ1 r2 θ2 : R,
  (Cpolar r1 θ1 * Cpolar r2 θ2 = Cpolar (r1 * r2) (θ1 + θ2))%C.
Proof.
  intros r1 θ1 r2 θ2.
  unfold Cpolar, Cmult; simpl.
  apply c_proj_eq; simpl.
  - rewrite cos_plus. ring.
  - rewrite sin_plus. ring.
Qed.

Theorem de_moivre : forall (r θ : R) (n : nat),
  ((Cpolar r θ) ^ n)%C = Cpolar (r ^ n) (n * θ).
Proof.
  intros r θ n.
  induction n as [| k IH].
  - simpl. unfold Cpolar. replace (0 * θ) with 0 by lra.
    rewrite cos_0, sin_0. apply c_proj_eq; simpl; lra.
  - replace ((Cpolar r θ ^ S k)%C) with ((Cpolar r θ * Cpolar r θ ^ k)%C) by reflexivity.
    rewrite IH. rewrite Cpolar_mult.
    apply c_proj_eq.
    + f_equal. f_equal. rewrite S_INR. lra.
    + f_equal. f_equal. rewrite S_INR. lra.
Qed.