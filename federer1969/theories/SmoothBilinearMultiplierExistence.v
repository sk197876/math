(** Federer (1969), 4.1.7, pp. 355–356: fixed smooth
    bilinear coefficient operations on actual fields. The
    original coordinate expansion proves existence; the
    public definition is independent of coordinates. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP NormRegularity
  LinearBasis SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothBilinearMultiplierUP
  FiniteSmoothBilinearConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SmoothBilinearExistence.
Variable R:realType.
Variables X Y1 Y2 Y3:lmodType R.
Variables (NX:X->R) (N1:Y1->R) (N2:Y2->R) (N3:Y3->R).
Hypotheses (hNX:is_real_norm NX) (hN1:is_real_norm N1)
  (hN2:is_real_norm N2) (hN3:is_real_norm N3).
Variable U:X->Prop.
Variables E1 E2 E3:lmodType R.
Variables (v1:E1->X->Y1) (v2:E2->X->Y2) (v3:E3->X->Y3).
Hypothesis hE1:is_smooth_function_space hNX hN1 U v1.
Hypothesis hE2:is_smooth_function_space hNX hN2 U v2.
Hypothesis hE3:is_smooth_function_space hNX hN3 U v3.
Hypothesis hFinite1:exists n,exists b:'I_n->Y1,is_basis b.
Hypothesis hFinite2:exists n,exists b:'I_n->Y2,is_basis b.
Variable B:Y1->Y2->Y3.
Hypothesis hB:bilinear B.
Variable u:E1.

(** Source for [smooth_bilinear_multiplier_exists]: the
    original smooth field product exists, supporting
    Federer 4.1.7, pp. 355–356. *)
Theorem smooth_bilinear_multiplier_exists:
  exists P:Hom E2 E3,is_smooth_bilinear_multiplier U v1 v2 v3 u B P.
Proof.
have [n1 [b1 hb1]]:=hFinite1; have [n2 [b2 hb2]]:=hFinite2.
exists (@finite_smooth_bilinear_witness R X Y1 Y2 Y3 NX N1 N2 N3
  hNX hN1 hN2 hN3 U E1 E2 E3 v1 v2 v3 hE1 hE2 hE3
  n1 n2 b1 b2 hb1 hb2 B hB u).
exact:finite_smooth_bilinear_witness_values.
Qed.
End SmoothBilinearExistence.
