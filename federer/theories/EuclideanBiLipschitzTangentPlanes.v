(** Federer (1969), 3.2.17, p. 254:
    the approximate tangent, ordinary tangent
    and differential image plane coincide. Combine
    the two proved inclusions, retaining actual
    restricted Hausdorff measure on the image. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  RealNormUP NormMetric HilbertFormCompactness NormDifferentialUP PartialFunctionUP
  MeasureUP MeasureBasic MeasureRestriction MeasureSetDensity CenteredBallRelations
  EuclideanLebesgueDimensions MetricDensities MetricDensityZeroPowerMass
  HausdorffMeasure MetricBiLipschitzUP TangentConeUP
  MeasureApproximateTangentUP MeasureApproximateTangentBasic
  EuclideanBiLipschitzOrdinaryPlane EuclideanBiLipschitzApproximatePlane.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_bilipschitz_tangent_planes]:
    the second displayed conclusion in Federer
    3.2.17, p. 254. The approximate
    cone is the exact cone of 3.2.16,
    rather than a plane chosen as a substitute. *)
Theorem euclidean_bilipschitz_tangent_planes (R : realType) m n
    (K : set (R_n R m)) (psi : R_n R m -> R_n R n) (lambda : R) a
    (L : Hom (R_n R m) (R_n R n)) :
  @is_metric_bilipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R m))
    (inner_metric_space (@euclidean_inner_productP R n)) K psi lambda ->
  0<lambda -> K a -> injective L ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT psi a L ->
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R m)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]) (~` K)) a 0%E ->
  measure_approximate_tangent_cone (inner_norm_real_norm (@euclidean_inner_productP R n))
    (measure_restrict (@hausdorff_measure R
      (inner_metric_space (@euclidean_inner_productP R n)) m) (psi @` K)) m (psi a)=
      norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) (psi @` K) (psi a) /\
  norm_tangent_cone (inner_norm (@euclidean_inner_productP R n)) (psi @` K) (psi a)=range L.
Proof.
move=> hB hLam ha hi hPsi hFull.
have hOrd := euclidean_bilipschitz_ordinary_tangent_plane hB hLam ha hi hPsi hFull.
split; last exact hOrd.
pose Y := inner_metric_space (@euclidean_inner_productP R n).
pose W := psi @` K.
pose H := @hausdorff_measure R Y m.
pose nu := measure_restrict H W.
have hm := @hausdorff_measure_is_measure R Y m.
have hn := measure_restrict_is_measure hm W.
have hNull : nu (~` W)=0%E.
  have heq : W `&` (~` W)=set0.
    apply/seteqP; split=> x; [by move=> [hx hn']; apply: hn'|by move=> []].
  by rewrite /nu /measure_restrict heq /H (measure_empty hm).
have hFullW := @null_set_metric_density_zero R
  (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) m
  nu (~` W) (psi a) hn hNull.
apply/seteqP; split=> v.
- move=> hv.
  exact: (@measure_approximate_tangent_ordinary R (R_n R n)
    (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) nu m (psi a) W hFullW v hv).
- move=> hv.
  have hr : range L v by rewrite -hOrd.
  exact: (@euclidean_bilipschitz_range_approximate_tangent R m n K psi lambda a L
    hB hLam ha hPsi hFull v hr).
Qed.
