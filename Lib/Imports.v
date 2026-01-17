Set Warnings "-all".

From Coq Require Export 
  (* Real numbers *)
  Reals 
  Lra 
  
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
  Logic.PropExtensionality
  Logic.ClassicalChoice
  Logic.ClassicalEpsilon
  
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
  Sets.Ensembles
  Sets.Classical_sets
  Sets.Powerset
  Sets.Finite_sets
  Sets.Image
  Lists.List.
  

Export ListNotations.
Import EqNotations.

Open Scope R_scope.
Open Scope nat_scope.