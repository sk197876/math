(** Federer (1969), 3.2.22(1), pp. 258–259:
    the exact image alternative at a regular source
    chart point with target-chart differential factorization. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormDifferentialUP NormDifferentialDirectional LinearRankAtLeast
  PartialFunctionUP PartialFunctionBasic PartialFunctionSourceRestriction PartialMetricLipschitz
  MeasureRestriction HausdorffMeasure MeasureApproximateDifferentialUP MeasureApproximateJacobianChart
  PartialLinearChartGraph PartialExteriorChartCoordinates PartialExteriorChartZero PartialExteriorPositiveChartImage
  EuclideanLinearJacobian ExteriorRankZero TopMiddleJacobianComposition
  RectifiableCompactChartsUP RectifiableCompactChartLaws RectifiableDifferentialChartUP
  RectifiableTargetChartBadRank RectifiableTangentPlaneUP RectifiableCoareaImageUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_chart_pair_image_point]:
    the two image alternatives at the end of
    p. 259 in Federer 3.2.22. The
    bad-target rank alternative makes the coordinate
    Jacobian zero. Otherwise a nonzero intrinsic Jacobian
    forces the coordinate differential onto and the actual
    partial differential image equals the target tangent
    plane, with its exact mu-dimensional vector-space laws. *)
Theorem rectifiable_chart_pair_image_point (R:realType) m n mu v
    (lambda:R) (W:set (R_n R n)) (Z:set (R_n R v)) (K:set (R_n R m))
    (psi:R_n R m->R_n R n) (F:R_n R n->R_n R v)
    (gamma:R_n R mu->R_n R v) a y
    (H0:Hom (R_n R m) (R_n R v)) (L:Hom (R_n R m) (R_n R mu))
    (Dt:Hom (R_n R mu) (R_n R v)):
  1<lambda ->is_uniform_compact_rectifiable_chart lambda K psi ->K a ->
  is_rectifiable_differential_chart_point W K psi F (psi a) ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R v)) setT (fun x=>F (psi x)) a H0 ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R mu))
    (inner_norm (@euclidean_inner_productP R v)) setT gamma y Dt ->
  gamma y=F (psi a) ->H0=hom_comp Dt L ->
  (rectifiable_target_chart_good_parameters Z gamma y \/ ~linear_rank_at_least L mu) ->
  is_rectifiable_coarea_image_point m mu W Z F (psi a).
Proof.
move=>hLambda hChart ha [b [Ds [H [d [hb [hValue [hInj [hDs [hH [hCone [hApx hComp]]]]]]]]]]]
  hH0 hDt hTargetValue hFactor hAlternative.
have hba:b=a:=@uniform_compact_chart_injective R m n lambda K psi hChart b a hb ha hValue.
rewrite hba in hDs hH.
have hHEq:H=H0:=@norm_differential_unique R (R_n R m) (R_n R v)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R v))
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R v)) setT (fun x=>F (psi x)) a H H0 hH hH0.
have hDom:=measure_approximate_differential_specification_domain hApx.
rewrite hCone in hDom; have hGraph:=partial_linear_chart_graph hDom hComp.
have [Lu [Ku [Kiu [hNorm _]]]]:=@partial_exterior_chart_coordinates_exists R m n v mu Ds H d hInj hGraph.
pose j:=euclidean_linear_jacobian mu Lu.
have [Ds0 [hDs0 hBounds]]:=rectifiable_chart_differential_bounds hChart ha.
have hDEq:Ds0=Ds:=@norm_differential_unique R (R_n R m) (R_n R n)
  (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R m))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) setT psi a Ds0 Ds hDs0 hDs.
rewrite hDEq in hBounds.
have hPositive:0<lambda:=lt_trans ltr01 hLambda.
have hHFactor:H=hom_comp Dt L:=eq_trans hHEq hFactor.
exists d,j; split; first exact hApx; split; first exact hNorm.
have [hGood|hLow]:=hAlternative.
- have [hj0|hj0]:=eqVneq j 0; first by left.
  have [hImage [P hPlane]]:=@partial_exterior_positive_chart_image R m n v mu Ds H L Dt d lambda j
    hInj hPositive hGraph (fun x=>(hBounds x).1) (fun x=>(hBounds x).2) hHFactor hNorm hj0.
  have hTangent:=hGood Dt hDt; rewrite hTargetValue in hTangent.
  right; split; first exact:(eq_trans hImage hTangent).
  exists P; by rewrite -hTangent.
- have hLZero:=euclidean_exterior_jacobian_rank_zero hLow.
  have hHZero:euclidean_linear_jacobian mu H=0.
    by rewrite hHFactor euclidean_top_middle_jacobian_compose hLZero mulr0.
  left; exact:(@partial_exterior_chart_jacobian_zero R m n v mu Ds H d lambda j
    hInj hPositive hGraph (fun x=>(hBounds x).1) (fun x=>(hBounds x).2) hNorm hHZero).
Qed.
