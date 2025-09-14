Set Warnings "-all".

(* Standard Library imports *)
From Coq Require Export 
  (* Real number theory *)
  Reals 
  Lra 
  Reals.ROrderedType
  Reals.Rdefinitions
  Reals.Raxioms
  Reals.Rfunctions
  Reals.SeqSeries
  Reals.Rtrigo
  Reals.Ranalysis
  
  (* Arithmetic *)
  ZArith
  QArith
  Arith.Arith
  Arith.PeanoNat
  Arith.Compare_dec
  Lia
  
  (* Logic *)
  Logic.Classical
  Logic.ClassicalFacts
  Logic.Classical_Pred_Type
  Logic.Classical_Prop
  Logic.FunctionalExtensionality
  Logic.ClassicalChoice
  
  (* Utilities *)
  String
  DecimalString
  Program
  Orders
  Sorting
  Permutation
  Utf8
  Classes.Morphisms

  (* Sets and Lists *)
  Lists.List
  Sets.Ensembles
  Sets.Classical_sets
  Sets.Powerset
  Sets.Finite_sets
  Sets.Image.
  

(* Common notations *)
Export ListNotations.
Import EqNotations.

(* Open common scopes *)
Open Scope R_scope.
Open Scope nat_scope.

Axiom EquivThenEqual: prop_extensionality.