(** Federer (1969), 2.9.19, pp. 163–165: almost-everywhere finite
    differentiability and condition (1), the signed variation quotient limit
    equals |g'|. The induced-measure alternative and the integral estimate
    are separate conclusions of the numbered theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength
  RealCurveDerivativeUP RealCurveVariationDerivative RealBVMonotoneDecomposition
  RealVariationDefectUP RealVariationDefectCover RealVariationDefectNullity RealDerivativeOrder
  MeasureAlmostUP MeasureAlmostBasic LebesgueScalarMeasure PositiveRightOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_bv_absolute_variation_derivative_ae]: direct finite
    differentiability and condition (1) in Federer 2.9.19, pp. 163–165 The
    monotone reduction gives simultaneous finite derivatives of g and s. The
    distance/variation inequality gives |g'|<=s'. Every point with s'>|g'|
    lies in some C_m, whose countable union is null by the fine near-maximal
    partition estimate. Thus s'=|g'| almost everywhere. The signed
    arc-length increment identity gives the printed two-sided variation
    quotient, including negative increments. *)
Theorem real_bv_absolute_variation_derivative_ae (R : realType)
    (g : R -> real_line_metric R) : curve_locally_finite_variation g ->
  measure_almost_everywhere (@lebesgue_scalar_measure R) [set x | exists v : R,
    has_real_curve_derivative g x v /\
    has_real_curve_derivative (arc_length g) x `|v| /\
    punctured_real_limit (fun h => fine (signed_curve_variation g x (x+h))/h) `|v|].
Proof.
move=> hg; have hm := lebesgue_scalar_is_measure R.
pose B := \bigcup_n real_variation_defect_locus g n.
have hBad : lebesgue_scalar_measure B=0%E := @real_variation_defect_union_null R g hg.
have hGood : measure_almost_everywhere (@lebesgue_scalar_measure R) (~` B).
  by rewrite /measure_almost_everywhere setCK.
have hJoint := @real_bv_joint_derivatives_ae R g hg.
have hBoth := measure_almost_everywhere_and hm hJoint hGood.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) (@lebesgue_scalar_measure R)
  hm _ _ _ hBoth).
move=> x [[v [w [hG [hS hw0]]]] hnB].
have hlow := @real_bv_derivative_variation_bound R g x v w hg hG hS.
have hupp : w<=`|v|.
  rewrite leNgt; apply/negP=> hgap.
  have [n hn] := @excess_arc_derivative_in_defect_locus R g x v w hG hS hgap.
  apply: hnB; by exists n.
have heq : w=`|v| by apply/le_anti/andP; split.
rewrite heq in hS.
exists v; split; first exact hG.
split; first exact hS.
exact ((@real_curve_variation_derivative_iff R g x `|v| hg).1 hS).
Qed.
