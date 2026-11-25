(** Federer (1969), 4.1.7, pp. 355–356:
    the independent pointwise law determines a
    continuous smooth operator. This public theorem
    uses only proved existence and uniqueness of
    values, without importing a construction module. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP LinearBasis
  SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothBilinearMultiplierUP
  ContinuousMultilinearSealed OpenFamilyTopologyUP SmoothFunctionDerivativesUP SmoothFunctionTopology
  SmoothBilinearContinuousExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SmoothBilinearContinuity.
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

Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Local Notation J2 := (fun j=>@ContinuousMultilinear.space R j X Y2 NX N2 hNX hN2).
Local Notation J3 := (fun j=>@ContinuousMultilinear.space R j X Y3 NX N3 hNX hN3).
Variable D:forall j,X->Hom E2 (J2 j).
Variable G:forall j,X->Hom E3 (J3 j).
Hypothesis hD:@is_smooth_function_derivatives R X Y2 NX N2 hNX hN2 U E2 v2 D.
Hypothesis hG:@is_smooth_function_derivatives R X Y3 NX N3 hNX hN3 U E3 v3 G.
Variable P:Hom E2 E3.
Hypothesis hP:is_smooth_bilinear_multiplier U v1 v2 v3 u B P.

(** Source for [smooth_bilinear_multiplier_continuous]:
    fixed smooth field operations are continuous for
    the original E topologies, supporting Federer
    4.1.7, pp. 355–356. No vector continuity of the
    literal final test topology is used. *)
Theorem smooth_bilinear_multiplier_continuous:
  open_family_continuous (smooth_function_opens hD) (smooth_function_opens hG) P.
Proof.
have [Q [hQ hContinuous]]:=@smooth_bilinear_continuous_multiplier_exists
  R X Y1 Y2 Y3 NX N1 N2 N3 hNX hN1 hN2 hN3 U E1 E2 E3 v1 v2 v3
  hE1 hE2 hE3 hFinite1 hFinite2 B hB u hU D G hD hG.
have hEq:P=Q.
  apply:hom_ext=>f;apply:(smooth_function_extensional hE3)=>x hx.
  by rewrite (@hP f x hx) (@hQ f x hx).
by rewrite hEq.
Qed.
End SmoothBilinearContinuity.
