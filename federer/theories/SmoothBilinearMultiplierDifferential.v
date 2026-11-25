(** Federer (1969), 4.1.7, p. 356: the two
    original smooth coefficient product rules used
    before transposition to currents. This is an
    application of the proved first bilinear calculus
    of 3.1.11, pp. 220–222. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP NormDifferentialLocal
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearOne
  NormHigherDifferentialUP NormHigherDifferentialFirst NormBoundedBilinearUP
  NormBilinearDifferentialAlgebra NormDifferentialBilinearProduct SmoothFunctionSpaceUP
  SmoothFunctionDerivativesUP SmoothDirectionalDerivativeUP SmoothDirectionalOrdinary
  SmoothBilinearMultiplierUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section SmoothBilinearDifferential.
Variable R:realType.
Variables X Y1 Y2 Y3:lmodType R.
Variables (NX:X->R) (N1:Y1->R) (N2:Y2->R) (N3:Y3->R).
Hypotheses (hNX:is_real_norm NX) (hN1:is_real_norm N1)
  (hN2:is_real_norm N2) (hN3:is_real_norm N3).
Variable U:set X.
Variables E1 E2 E3:lmodType R.
Variables (v1:E1->X->Y1) (v2:E2->X->Y2) (v3:E3->X->Y3).
Local Notation J1 := (fun j=>@ContinuousMultilinear.space R j X Y1 NX N1 hNX hN1).
Local Notation J2 := (fun j=>@ContinuousMultilinear.space R j X Y2 NX N2 hNX hN2).
Local Notation J3 := (fun j=>@ContinuousMultilinear.space R j X Y3 NX N3 hNX hN3).
Variable D1:forall j,X->Hom E1 (J1 j).
Variable D2:forall j,X->Hom E2 (J2 j).
Variable D3:forall j,X->Hom E3 (J3 j).
Hypothesis hD1:@is_smooth_function_derivatives R X Y1 NX N1 hNX hN1 U E1 v1 D1.
Hypothesis hD2:@is_smooth_function_derivatives R X Y2 NX N2 hNX hN2 U E2 v2 D2.
Hypothesis hD3:@is_smooth_function_derivatives R X Y3 NX N3 hNX hN3 U E3 v3 D3.
Variable v:X.
Variables (P1:Hom E1 E1) (P2:Hom E2 E2) (P3:Hom E3 E3).
Hypothesis hP1:@is_smooth_directional_derivative R X Y1 NX N1 hNX hN1 U E1 v1 D1 v P1.
Hypothesis hP2:@is_smooth_directional_derivative R X Y2 NX N2 hNX hN2 U E2 v2 D2 v P2.
Hypothesis hP3:@is_smooth_directional_derivative R X Y3 NX N3 hNX hN3 U E3 v3 D3 v P3.
Variable B:Y1->Y2->Y3.
Hypothesis hB:norm_bounded_bilinear N1 N2 N3 B.
Variable u:E1.
Variable W:Hom E2 E3.
Hypothesis hW:is_smooth_bilinear_multiplier U v1 v2 v3 u B W.

(** Source for [smooth_bilinear_multiplier_directional_values]:
    the original directional product rule, supporting
    both current product identities of Federer 4.1.7,
    p. 356. All terms are actual smooth derivatives. *)
Theorem smooth_bilinear_multiplier_directional_values f x:U x->
  v3 (P3 (W f)) x=B (v1 (P1 u) x) (v2 f x)+B (v1 u x) (v2 (P2 f) x).
Proof.
move=>hx.
pose L1:=@continuous_multilinear_one_operator R X Y1 (J1 1%N) NX N1
  (@ContinuousMultilinear.evaluation R 1%N X Y1 NX N1 hNX hN1)
  (@ContinuousMultilinear.norm R 1%N X Y1 NX N1 hNX hN1)
  (@ContinuousMultilinear.laws R 1%N X Y1 NX N1 hNX hN1) (@D1 1%N x u).
pose L2:=@continuous_multilinear_one_operator R X Y2 (J2 1%N) NX N2
  (@ContinuousMultilinear.evaluation R 1%N X Y2 NX N2 hNX hN2)
  (@ContinuousMultilinear.norm R 1%N X Y2 NX N2 hNX hN2)
  (@ContinuousMultilinear.laws R 1%N X Y2 NX N2 hNX hN2) (@D2 1%N x f).
have hL1:has_norm_differential NX N1 U (v1 u) x L1.
  exact:((@norm_higher_differential_first R X Y1 NX N1 hNX hN1 J1
    (fun j=>@ContinuousMultilinear.evaluation R j X Y1 NX N1 hNX hN1)
    (fun j=>@ContinuousMultilinear.norm R j X Y1 NX N1 hNX hN1)
    (fun j=>@ContinuousMultilinear.laws R j X Y1 NX N1 hNX hN1) U (v1 u) x _).1
      (@smooth_derivative_exact R X Y1 NX N1 hNX hN1 U E1 v1 D1 hD1 1%N u x hx)).
have hL2:has_norm_differential NX N2 U (v2 f) x L2.
  exact:((@norm_higher_differential_first R X Y2 NX N2 hNX hN2 J2
    (fun j=>@ContinuousMultilinear.evaluation R j X Y2 NX N2 hNX hN2)
    (fun j=>@ContinuousMultilinear.norm R j X Y2 NX N2 hNX hN2)
    (fun j=>@ContinuousMultilinear.laws R j X Y2 NX N2 hNX hN2) U (v2 f) x _).1
      (@smooth_derivative_exact R X Y2 NX N2 hNX hN2 U E2 v2 D2 hD2 1%N f x hx)).
have [C [hC hBound]]:=hB.2.
pose L:=norm_bilinear_product_linear_term hB.1 (v1 u x) (v2 f x) L1 L2.
have hProd:=@norm_differential_bilinear_product R X Y1 Y2 Y3 NX N1 N2 N3
  hNX hN1 hN2 hN3 B hB.1 C U (v1 u) (v2 f) x L1 L2 hC hBound hL1 hL2.
have hActual:has_norm_differential NX N3 U (v3 (W f)) x L.
  exact:(norm_differential_domain_agreement hNX (fun y hy=>esym (@hW f y hy)) hProd).
have hOut:=@smooth_directional_ordinary_evaluation R X Y3 NX N3 hNX hN3 U E3 v3 D3 hD3
  v P3 hP3 (W f) x L hx hActual.
have hIn1:=@smooth_directional_ordinary_evaluation R X Y1 NX N1 hNX hN1 U E1 v1 D1 hD1
  v P1 hP1 u x L1 hx hL1.
have hIn2:=@smooth_directional_ordinary_evaluation R X Y2 NX N2 hNX hN2 U E2 v2 D2 hD2
  v P2 hP2 f x L2 hx hL2.
rewrite hOut hIn1 hIn2; reflexivity.
Qed.
End SmoothBilinearDifferential.
