From Lib Require Import Imports Sets Notations.
Import SetNotations.

Local Notation In := Ensembles.In.

Open Scope set_scope.

Module FunctionNotations.

  Notation "f ∘ g" := (compose f g) (at level 40, left associativity) : function_scope.
  Notation "f + g" := (fun x : ℝ => f x + g x) (at level 50, left associativity) : function_scope.
  Notation "f - g" := (fun x : ℝ => f x - g x) (at level 50, left associativity) : function_scope.
  Notation "- f" := (fun x : ℝ => - f x) (at level 35) : function_scope.
  Notation "f ⋅ g" := (fun x : ℝ => f x * g x) (at level 40, left associativity) : function_scope. 
  Notation "c * f" := (fun x : ℝ => c * f x) (at level 40, left associativity) : function_scope. 
  Notation "f / g" := (fun x : ℝ => f x / g x) (at level 40, left associativity) : function_scope.
  Notation "f ^ n" := (fun x : ℝ => (f x) ^ n) (at level 30, right associativity) : function_scope.
  Notation "∕ f" := (fun x : ℝ => 1 / f x) (at level 40, left associativity) : function_scope.

End FunctionNotations.

Import FunctionNotations.

Definition even_f (f : R -> R) : Prop := ∀ x, f (-x) = f x.

Definition odd_f (f : R -> R) : Prop := ∀ x, f (-x) = - (f x).

Lemma f_subtype_independent {U V} (P : Ensemble U) (f : subType P -> V) (x : U) (H1 H2 : In _ P x) :
  f {| val := x; property := H1 |} = f {| val := x; property := H2 |}.
Proof.
  assert ({| val := x; property := H1 |} = {| val := x; property := H2 |}) as H3 by (f_equal; apply proof_irrelevance).
  rewrite H3. reflexivity.
Qed.

Definition maps_into {A B : Type} (f : A -> B) (D : Ensemble A) (C : Ensemble B) : Prop :=
  forall x, x ∈ D -> f x ∈ C.

Definition injective_on {A B : Type} (f : A -> B) (D : Ensemble A) : Prop :=
  forall x y : A, x ∈ D -> y ∈ D -> f x = f y -> x = y.

Definition surjective_on {A B : Type} (f : A -> B) (D : Ensemble A) (C : Ensemble B) : Prop :=
  forall y : B, y ∈ C -> exists x : A, x ∈ D /\ f x = y.

Definition bijective_on {A B : Type} (f : A -> B) (D : Ensemble A) (C : Ensemble B) : Prop :=
  maps_into f D C /\ injective_on f D /\ surjective_on f D C.

Lemma injective_subType : forall U V (A : Ensemble U) (f : U -> V),
  injective_on f A -> injective (fun x : subType A => f (val A x)).
Proof.
  intros U V A f H1. unfold injective. intros x y H2. destruct x as [x H3], y as [y H4]. simpl in *.
  specialize (H1 x y H3 H4 H2). subst. replace H3 with H4. 2 : { apply proof_irrelevance. } reflexivity.
Qed.

Lemma bijective_subType : forall U V (f : U -> V),
  bijective f -> bijective (fun x : subType (Full_set U) => mkSubType V (Full_set V) (f (val (Full_set U) x)) ltac:(apply Full_intro)).
Proof.
  intros U V f [H1 H2]. split.
  - intros [x H3] [y H4] H5; simpl in *. specialize (H1 x y). injection H5; intros H6. specialize (H1 H6). subst.
    replace H3 with H4. 2 : { apply proof_irrelevance. } reflexivity.
  - intros [y H3]. specialize (H2 y) as [x H4]. exists (mkSubType U (Full_set U) x ltac:(apply Full_intro)). simpl. destruct H3, H4. reflexivity.
Qed.

Lemma exists_bijection : ∀ (U V : Type) (f : U -> V),
  bijective f -> exists f : subType (Full_set U) -> subType (Full_set V), bijective f.
Proof.
  intros U V f H1. set (g := fun x : subType (Full_set U) => mkSubType V (Full_set V) (f (val (Full_set U) x)) ltac:(apply Full_intro)).
  exists g. apply bijective_subType. auto.
Qed.

Lemma eq_cardinality_Full_set : forall (A B : Type),
  ((exists f : A -> B, bijective f) /\ (exists (a : A) (b : B), True)) \/ ((Full_set A = ∅) /\ (Full_set B = ∅)) -> ‖Full_set A‖ = ‖Full_set B‖.
Proof.
  intros A B [[[f [H1 H2]] [a [b _]]] | H2].
  - unfold injective in H1. unfold surjective in H2. right; 
  unfold cardinal_eq. repeat split. assert (H3 : a ∈ Full_set A) by apply Full_intro. intros H4. rewrite H4 in H3. autoset.
  assert (H3 : b ∈ Full_set B) by apply Full_intro. intros H4. rewrite H4 in H3. autoset.
  exists (fun sa : subType (Full_set A) => mkSubType B (Full_set B) (f (val _ sa)) ltac:(apply Full_intro)).
  split.
  -- intros x y H3. destruct x as [x H4], y as [y H5]. simpl in *. specialize (H1 x y).
    specialize (H1 ltac:(inversion H3; reflexivity)). subst. replace H4 with H5.
    2 : { destruct H4, H5. reflexivity. } reflexivity.
  -- intros y. destruct y as [y H3]. specialize (H2 y) as [x H4]. exists (mkSubType A (Full_set A) x ltac:(apply Full_intro)).
    simpl. destruct H3, H4. reflexivity.
  - left. split; destruct H2; auto.
Qed.

Coercion Type_to_Ensemble (A : Type) : Ensemble A :=
  Full_set A.

Lemma eq_cardinality_Full_set_Type : forall (A B : Type),
  ‖A‖ = ‖B‖ <-> ‖Full_set A‖ = ‖Full_set B‖.
Proof.
  intros A B. split; intro H1; unfold Type_to_Ensemble in H1; auto.
Qed.

Lemma eq_cardinality_Type : forall A B : Type,
  ((exists f : A -> B, bijective f) /\ (exists (a : A) (b : B), True)) \/ ((Full_set A = ∅) /\ (Full_set B = ∅)) -> ‖A‖ = ‖B‖.
Proof.
  intros A B [[[f H1] [a [b _]]] | [H1 H2]]; apply eq_cardinality_Full_set; auto. left. split. exists f. auto. exists a, b. auto.
Qed.

Theorem theorem_28_1 : forall A B (f : A -> B),
  Finite_set (Full_set A) -> ‖ image f ‖ <= ‖ (Full_set A) ‖.
Proof.
  intros A B f H1.
Abort.