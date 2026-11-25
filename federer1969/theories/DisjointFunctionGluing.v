(** Public interface for disjoint density gluing in Federer (1969), 2.5.10,
    p. 101 Source context and conventions: DisjointFunctionGluingUP.v.
    Downstream results use agreement and zero-extension laws only. *)
From mathcomp Require Import all_boot all_algebra classical_sets reals.
From Federer Require Import DisjointFunctionGluingUP DisjointFunctionGluingSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [disjoint_function_gluing]: public witness for
    the density sum in Federer 2.5.10, p. 101. *)
Definition disjoint_function_gluing (R : realType) (X J : Type)
    (D : set J) (B : J -> set X) (f : J -> X -> R)
    (hd : forall i j, D i -> D j -> i <> j -> B i `&` B j=set0) :=
  @DisjointFunctionGluing.value R X J D B f hd.

(** Source for [disjoint_function_gluing_specification]: public
    agreement and zero-extension laws supporting Federer 2.5.10, p. 101. *)
Lemma disjoint_function_gluing_specification (R : realType) (X J : Type)
    (D : set J) (B : J -> set X) (f : J -> X -> R)
    (hd : forall i j, D i -> D j -> i <> j -> B i `&` B j=set0) :
  is_disjoint_function_gluing D B f (@disjoint_function_gluing R X J D B f hd).
Proof. exact: (@DisjointFunctionGluing.laws R X J D B f hd). Qed.
