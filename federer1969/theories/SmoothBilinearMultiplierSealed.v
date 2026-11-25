(** Federer (1969), 4.1.7, pp. 355–356: fixed smooth
    bilinear coefficient operations on actual fields. The
    original coordinate expansion proves existence; the
    public definition is independent of coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP NormRegularity
  LinearBasis SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothBilinearMultiplierUP
  SmoothBilinearMultiplierExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Module Type SmoothBilinearMultiplierSignature.
(** Source for [operator]: the original fixed smooth
    field operation, supporting Federer 4.1.7,
    pp. 355–356. *)
Parameter operator:forall (R:realType) (X Y1 Y2 Y3:lmodType R)
    (NX:X->R) (N1:Y1->R) (N2:Y2->R) (N3:Y3->R)
    (hNX:is_real_norm NX) (hN1:is_real_norm N1)
    (hN2:is_real_norm N2) (hN3:is_real_norm N3)
    (U:X->Prop) (E1 E2 E3:lmodType R)
    (v1:E1->X->Y1) (v2:E2->X->Y2) (v3:E3->X->Y3)
    (hE1:is_smooth_function_space hNX hN1 U v1)
    (hE2:is_smooth_function_space hNX hN2 U v2)
    (hE3:is_smooth_function_space hNX hN3 U v3)
    (hFinite1:exists n,exists b:'I_n->Y1,is_basis b)
    (hFinite2:exists n,exists b:'I_n->Y2,is_basis b)
    (B:Y1->Y2->Y3) (hB:bilinear B) (u:E1),Hom E2 E3.
(** Source for [laws]: exact original pointwise action,
    supporting Federer 4.1.7, pp. 355–356. *)
Parameter laws:forall (R:realType) (X Y1 Y2 Y3:lmodType R)
    (NX:X->R) (N1:Y1->R) (N2:Y2->R) (N3:Y3->R)
    (hNX:is_real_norm NX) (hN1:is_real_norm N1)
    (hN2:is_real_norm N2) (hN3:is_real_norm N3)
    (U:X->Prop) (E1 E2 E3:lmodType R)
    (v1:E1->X->Y1) (v2:E2->X->Y2) (v3:E3->X->Y3)
    (hE1:is_smooth_function_space hNX hN1 U v1)
    (hE2:is_smooth_function_space hNX hN2 U v2)
    (hE3:is_smooth_function_space hNX hN3 U v3)
    (hFinite1:exists n,exists b:'I_n->Y1,is_basis b)
    (hFinite2:exists n,exists b:'I_n->Y2,is_basis b)
    (B:Y1->Y2->Y3) (hB:bilinear B) (u:E1),
  is_smooth_bilinear_multiplier U v1 v2 v3 u B
    (@operator R X Y1 Y2 Y3 NX N1 N2 N3 hNX hN1 hN2 hN3 U E1 E2 E3 v1 v2 v3 hE1 hE2 hE3 hFinite1 hFinite2 B hB u).
End SmoothBilinearMultiplierSignature.
Module SmoothBilinearMultiplier:SmoothBilinearMultiplierSignature.
(** Source for [operator]: seal the proved existence
    witness, supporting Federer 4.1.7, pp. 355–356. *)
Definition operator (R:realType) (X Y1 Y2 Y3:lmodType R)
    (NX:X->R) (N1:Y1->R) (N2:Y2->R) (N3:Y3->R)
    (hNX:is_real_norm NX) (hN1:is_real_norm N1)
    (hN2:is_real_norm N2) (hN3:is_real_norm N3)
    (U:X->Prop) (E1 E2 E3:lmodType R)
    (v1:E1->X->Y1) (v2:E2->X->Y2) (v3:E3->X->Y3)
    (hE1:is_smooth_function_space hNX hN1 U v1)
    (hE2:is_smooth_function_space hNX hN2 U v2)
    (hE3:is_smooth_function_space hNX hN3 U v3)
    (hFinite1:exists n,exists b:'I_n->Y1,is_basis b)
    (hFinite2:exists n,exists b:'I_n->Y2,is_basis b)
    (B:Y1->Y2->Y3) (hB:bilinear B) (u:E1):Hom E2 E3:=
  projT1 (cid (@smooth_bilinear_multiplier_exists R X Y1 Y2 Y3 NX N1 N2 N3 hNX hN1 hN2 hN3 U E1 E2 E3 v1 v2 v3 hE1 hE2 hE3 hFinite1 hFinite2 B hB u)).
(** Source for [laws]: the sealed operator has the
    independent original value law, supporting
    Federer 4.1.7, pp. 355–356. *)
Lemma laws (R:realType) (X Y1 Y2 Y3:lmodType R)
    (NX:X->R) (N1:Y1->R) (N2:Y2->R) (N3:Y3->R)
    (hNX:is_real_norm NX) (hN1:is_real_norm N1)
    (hN2:is_real_norm N2) (hN3:is_real_norm N3)
    (U:X->Prop) (E1 E2 E3:lmodType R)
    (v1:E1->X->Y1) (v2:E2->X->Y2) (v3:E3->X->Y3)
    (hE1:is_smooth_function_space hNX hN1 U v1)
    (hE2:is_smooth_function_space hNX hN2 U v2)
    (hE3:is_smooth_function_space hNX hN3 U v3)
    (hFinite1:exists n,exists b:'I_n->Y1,is_basis b)
    (hFinite2:exists n,exists b:'I_n->Y2,is_basis b)
    (B:Y1->Y2->Y3) (hB:bilinear B) (u:E1):
  is_smooth_bilinear_multiplier U v1 v2 v3 u B
    (@operator R X Y1 Y2 Y3 NX N1 N2 N3 hNX hN1 hN2 hN3 U E1 E2 E3 v1 v2 v3 hE1 hE2 hE3 hFinite1 hFinite2 B hB u).
Proof. exact:(projT2 (cid (@smooth_bilinear_multiplier_exists R X Y1 Y2 Y3 NX N1 N2 N3 hNX hN1 hN2 hN3 U E1 E2 E3 v1 v2 v3 hE1 hE2 hE3 hFinite1 hFinite2 B hB u))). Qed.
End SmoothBilinearMultiplier.
