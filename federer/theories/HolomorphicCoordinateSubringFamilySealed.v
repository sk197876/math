(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(1), p. 326:
    the original coordinate subring family behind
    its independent opaque image interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP Hom RealNormUP LinearBasis HolomorphicGermRing
  HolomorphicCoordinateSubringFamilyUP HolomorphicCoordinateSubringFamilyExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type HolomorphicCoordinateSubringFamilySignature.
(** Source for [value]: the original Q_j family,
    3.4.8(1), p. 326. *)
Parameter value:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX)
  n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X (ComplexScalars.C R)^o),
  nat->set (@holomorphic_germ_ring R X NX hNX 0).
(** Source for [laws]: exact original prefix-image
    laws, 3.4.8(1), p. 326. *)
Parameter laws:forall (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX)
  n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X (ComplexScalars.C R)^o),
  is_holomorphic_coordinate_subring_family he omega (@value R X NX hNX n e he omega).
End HolomorphicCoordinateSubringFamilySignature.
Module HolomorphicCoordinateSubringFamily:HolomorphicCoordinateSubringFamilySignature.
(** Source for [value]: a hidden witness of
    proved family existence, 3.4.8(1), p. 326. *)
Definition value (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX)
  n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X (ComplexScalars.C R)^o):=
  projT1 (cid (@holomorphic_coordinate_subring_family_exists R X NX hNX n e he omega)).
(** Source for [laws]: the hidden family satisfies
    the independent image laws, 3.4.8(1), p. 326. *)
Lemma laws (R:realType) (X:lmodType (ComplexScalars.C R)) (NX:X->R) (hNX:@is_real_norm R (restricted_space (ComplexScalars.embed R) X) NX)
  n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X (ComplexScalars.C R)^o):
  is_holomorphic_coordinate_subring_family he omega (@value R X NX hNX n e he omega).
Proof. exact:(projT2 (cid (@holomorphic_coordinate_subring_family_exists R X NX hNX n e he omega))). Qed.
End HolomorphicCoordinateSubringFamily.
