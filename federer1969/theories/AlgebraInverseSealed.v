(** Opaque partial inversion for Federer (1969),
    3.1.11, p. 220. Only its exact two-sided
    inverse laws cross the construction boundary. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import AlgebraUP PartialFunctionUP AlgebraInverseUP AlgebraInverseConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Type AlgebraInverseSignature.
(** Source for [value]: the partial inversion operation
    used in Federer 3.1.11, p. 220. *)
Parameter value : forall (K : fieldType) (A : algebra K), partial_function A A.
(** Source for [laws]: exact inverse values and domain,
    supporting Federer 3.1.11, p. 220. *)
Parameter laws : forall (K : fieldType) (A : algebra K),
  is_algebra_inverse_graph (@value K A).
End AlgebraInverseSignature.

Module AlgebraInverse : AlgebraInverseSignature.
(** Source for [value]: privately selected proved graph
    for inversion, Federer 3.1.11, p. 220. *)
Definition value (K : fieldType) (A : algebra K) :=
  projT1 (cid (@algebra_inverse_graph_exists K A)).
(** Source for [laws]: the selected graph obeys exactly
    the two inverse identities, Federer 3.1.11, p. 220. *)
Lemma laws (K : fieldType) (A : algebra K) :
  is_algebra_inverse_graph (@value K A).
Proof. exact: projT2 (cid (@algebra_inverse_graph_exists K A)). Qed.
End AlgebraInverse.
