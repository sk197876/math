(** Federer (1969), 3.4.8(1), p. 326:
    actual coordinate germs behind their independent
    opaque representative equations. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP LinearBasis AnalyticGermRing
  AnalyticCoordinateGermsUP AnalyticCoordinateGermsExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Module Type AnalyticCoordinateGermsSignature.
(** Source for [value]: the original gamma_j germs,
    3.4.8(1), p. 326, with the published
    dual-space correction. *)
Parameter value:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X R^o),
  'I_n->@analytic_germ_ring R X NX hNX 0.
(** Source for [laws]: every original linear-coordinate
    representative gives the corresponding actual germ,
    3.4.8(1), p. 326. *)
Parameter laws:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X R^o),
  is_analytic_coordinate_germs omega (@value R X NX hNX n e he omega).
End AnalyticCoordinateGermsSignature.
Module AnalyticCoordinateGerms:AnalyticCoordinateGermsSignature.
(** Source for [value]: private choice from proved
    actual existence, 3.4.8(1), p. 326. *)
Definition value (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X R^o):=
  projT1 (cid (@analytic_coordinate_germs_exist R X NX hNX n e he omega)).
(** Source for [laws]: the private family satisfies
    every independent representative equation,
    3.4.8(1), p. 326. *)
Lemma laws (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  n (e:'I_n->X) (he:is_basis e) (omega:'I_n->Hom X R^o):
  is_analytic_coordinate_germs omega (@value R X NX hNX n e he omega).
Proof. exact:(projT2 (cid (@analytic_coordinate_germs_exist R X NX hNX n e he omega))). Qed.
End AnalyticCoordinateGerms.
