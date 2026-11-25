(** Federer (1969), 4.1.7, pp. 355–356:
    the original smooth bilinear operator has a
    continuous witness. The coordinate construction is
    used only inside this existence proof; later
    consumers use the independent pointwise law. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP NormRegularity
  LinearBasis SmoothFunctionSpaceUP SmoothFunctionSpaceLaws SmoothBilinearMultiplierUP
  FiniteSmoothBilinearConstruction ContinuousMultilinearSealed OpenFamilyTopologyUP
  SmoothFunctionDerivativesUP SmoothFunctionTopology OpenFamilyFiniteHomSum
  SmoothMultiplierUP SmoothMultiplierSealed SmoothMultiplierContinuity
  SmoothTargetOperatorUP SmoothTargetOperatorSealed SmoothTargetOperatorContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section SmoothBilinearContinuousExistence.
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

(** Source for [smooth_bilinear_continuous_multiplier_exists]:
    a continuous operator has the exact original
    fixed-field action, supporting Federer 4.1.7,
    pp. 355–356. The proof uses the original
    finite coordinate expansion, scalar multipliers
    and bounded constant coefficient maps. *)
Theorem smooth_bilinear_continuous_multiplier_exists:
  exists P:Hom E2 E3,is_smooth_bilinear_multiplier U v1 v2 v3 u B P /\
    open_family_continuous (smooth_function_opens hD) (smooth_function_opens hG) P.
Proof.
have [n1 [b1 hb1]]:=hFinite1; have [n2 [b2 hb2]]:=hFinite2.
pose W:=@finite_smooth_bilinear_witness R X Y1 Y2 Y3 NX N1 N2 N3
  hNX hN1 hN2 hN3 U E1 E2 E3 v1 v2 v3 hE1 hE2 hE3 n1 n2 b1 b2 hb1 hb2 B hB u.
have hW:is_smooth_bilinear_multiplier U v1 v2 v3 u B W:=
  @finite_smooth_bilinear_witness_values R X Y1 Y2 Y3 NX N1 N2 N3
    hNX hN1 hN2 hN3 U E1 E2 E3 v1 v2 v3 hE1 hE2 hE3 n1 n2 b1 b2 hb1 hb2 B hB u.
exists W;split;first exact:hW.
rewrite /W /finite_smooth_bilinear_witness.
apply:(open_family_finite_hom_sum_continuous
  (smooth_function_topology_laws hD).1 (smooth_function_topology_vector hG))=>i.
rewrite /finite_smooth_bilinear_term.
apply:(@open_family_continuous_compose E2 E2 E3 (smooth_function_opens hD)
  (smooth_function_opens hD) (smooth_function_opens hG) _ _).
- rewrite /finite_smooth_bilinear_scalar_operator.
  exact (@smooth_multiplier_continuous R X Y2 NX N2 hNX hN2 U hU E2 v2 hE2 D hD
    (@finite_smooth_bilinear_scalar R X Y1 E1 v1 n1 b1 hb1 u i) (finite_smooth_bilinear_scalar_regular hE1 hb1 u i)
    _ (@SmoothMultiplier.laws R X Y2 NX N2 hNX hN2 U E2 v2 hE2
      (@finite_smooth_bilinear_scalar R X Y1 E1 v1 n1 b1 hb1 u i) (finite_smooth_bilinear_scalar_regular hE1 hb1 u i))).
- rewrite /finite_smooth_bilinear_target_operator.
  exact (@smooth_target_operator_continuous R X Y2 Y3 NX N2 N3 hNX hN2 hN3 U E2 E3 v2 v3 hE2 hE3
    D G hD hG _ (@finite_smooth_bilinear_left_bounded R Y1 Y2 Y3 N2 N3 hN2 hN3 n1 n2 b1 b2 hb2 B hB i)
    _ (SmoothTargetOperator.laws _ _ _)).
Qed.
End SmoothBilinearContinuousExistence.
