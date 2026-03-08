From Calculus.Chapter8 Require Import Prelude.

Lemma lemma_8_2_a_1 : forall A, A ≠ ∅ -> has_lower_bound A -> (fun x => -x ∈ A) ≠ ∅.
Proof. Admitted.

Lemma lemma_8_2_a_2 : forall A, A ≠ ∅ -> has_lower_bound A -> has_upper_bound (fun x => -x ∈ A).
Proof. Admitted.

Lemma lemma_8_2_a_3 : forall A sup, A ≠ ∅ -> has_lower_bound A -> is_lub (fun x => -x ∈ A) sup -> is_glb A (-sup).
Proof. Admitted.

Lemma lemma_8_2_b_1 : forall A, A ≠ ∅ -> has_lower_bound A -> (fun x => is_lower_bound A x) ≠ ∅.
Proof. Admitted.

Lemma lemma_8_2_b_2 : forall A, A ≠ ∅ -> has_lower_bound A -> has_upper_bound (fun x => is_lower_bound A x).
Proof. Admitted.

Lemma lemma_8_2_b_3 : forall A sup, A ≠ ∅ -> has_lower_bound A -> is_lub (fun x => is_lower_bound A x) sup -> is_glb A sup.
Proof. Admitted.
