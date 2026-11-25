(** Federer (1969), 3.4.8(1), p. 326:
    the original coordinate subring family behind
    its independent opaque image interface. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearBasis AnalyticGermRing
  AnalyticCoordinateSubringFamilyUP AnalyticCoordinateSubringFamilyExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type AnalyticCoordinateSubringFamilySignature.
(** Source for [value]: the original Q_j family,
    3.4.8(1), p. 326. *)
Parameter value:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X R^o),
  nat->set (@analytic_germ_ring R X NX hNX 0).
(** Source for [laws]: exact original prefix-image
    laws, 3.4.8(1), p. 326. *)
Parameter laws:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X R^o),
  is_analytic_coordinate_subring_family he omega (@value R X NX hNX n e he omega).
End AnalyticCoordinateSubringFamilySignature.
Module AnalyticCoordinateSubringFamily:AnalyticCoordinateSubringFamilySignature.
(** Source for [value]: a hidden witness of
    proved family existence, 3.4.8(1), p. 326. *)
Definition value (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X R^o):=
  projT1 (cid (@analytic_coordinate_subring_family_exists R X NX hNX n e he omega)).
(** Source for [laws]: the hidden family satisfies
    the independent image laws, 3.4.8(1), p. 326. *)
Lemma laws (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X R^o):
  is_analytic_coordinate_subring_family he omega (@value R X NX hNX n e he omega).
Proof. exact:(projT2 (cid (@analytic_coordinate_subring_family_exists R X NX hNX n e he omega))). Qed.
End AnalyticCoordinateSubringFamily.
