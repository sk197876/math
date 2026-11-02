(** Opaque interface for the disjoint density gluing in Federer (1969),
    2.5.10, p. 101. Source context and conventions:
    DisjointFunctionGluingUP.v. Only the witness and its laws are exposed. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets reals.
From Federer Require Import DisjointFunctionGluingUP DisjointFunctionGluingConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Module Type DisjointFunctionGluingSignature.
(** Source for [value]: abstract glued density in Federer
    2.5.10, p. 101, first paragraph. *)
Parameter value : forall (R : realType) (X J : Type) (D : set J) (B : J -> set X)
    (f : J -> X -> R),
  (forall i j, D i -> D j -> i <> j -> B i `&` B j=set0) -> X -> R.
(** Source for [laws]: agreement and zero-extension laws supporting
    Federer 2.5.10, p. 101, first paragraph. *)
Parameter laws : forall (R : realType) (X J : Type) (D : set J) (B : J -> set X)
    (f : J -> X -> R)
    (hd : forall i j, D i -> D j -> i <> j -> B i `&` B j=set0),
  is_disjoint_function_gluing D B f (@value R X J D B f hd).
End DisjointFunctionGluingSignature.
Module DisjointFunctionGluing : DisjointFunctionGluingSignature.
(** Source for [value]: private witness selection from the proved
    gluing existence supporting Federer 2.5.10, p. 101. *)
Definition value (R : realType) (X J : Type) (D : set J) (B : J -> set X)
    (f : J -> X -> R)
    (hd : forall i j, D i -> D j -> i <> j -> B i `&` B j=set0) :=
  projT1 (cid (@disjoint_function_gluing_exists R X J D B f hd)).
(** Source for [laws]: the selected witness satisfies the abstract
    laws for Federer 2.5.10, p. 101. *)
Lemma laws (R : realType) (X J : Type) (D : set J) (B : J -> set X)
    (f : J -> X -> R)
    (hd : forall i j, D i -> D j -> i <> j -> B i `&` B j=set0) :
  is_disjoint_function_gluing D B f (@value R X J D B f hd).
Proof. exact: projT2 (cid (@disjoint_function_gluing_exists R X J D B f hd)). Qed.
End DisjointFunctionGluing.
