(** Federer (1969), 3.3.18, p. 301: the original
    normal cone has ordinary zero density at a tangent-plane point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces ModuleQuotient
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness InnerNormalization
  RealNormUP NormMetric MetricSetDistanceSealed MetricSetDistanceUP MetricSetDistanceBasic SubspaceDistanceSeminorm
  StructureCone StructureConeBasic MeasureUP MeasureRestriction PartialFunctionUP MetricDensities
  MetricDensityZeroUnions MeasureApproximateTangentUP MeasureApproximateNormalUP
  RectifiableTangentPlaneUP CompactNontangentDirections ApproximateNormalUnitDirections
  ConeAngleUnitNormalization.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [approximate_normal_cone_zero_density]: the final
    implication in Federer 3.3.18, p. 301. Actual compact unit
    directions at distance at most s from the original normal avoid
    the original tangent plane. Actual 3.2.16 makes their positive
    hull zero-density. The ORIGINAL strict cone lies in that hull,
    giving its ordinary zero density for every 0<s<1. Square
    brackets in the book merely delimit X's arguments; the vertex
    is still excluded. No finite-density or positive-degree premise
    is needed in this geometric implication. *)
Theorem approximate_normal_cone_zero_density (R:realType) n m k
    (mu:set (R_n R n)->\bar R) (a:R_n R n) (N:G (R_n R n) k) (s:R):
  is_measure mu ->is_m_dimensional_approximate_tangent m mu a ->
  (forall u,grassmann_val N u <->measure_approximate_normal_cone (@euclidean_inner_productP R n) mu m a u) ->
  (0<s<1)%R ->
  partial_function_graph (@metric_density R (inner_metric_space (@euclidean_inner_productP R n)) m
    (measure_restrict mu (structure_cone N a +oo s))) a 0%E.
Proof.
move=>hMu [T hT] hN /andP[hs hs1].
pose X:=inner_metric_space (@euclidean_inner_productP R n).
pose NX:=inner_norm (@euclidean_inner_productP R n).
pose A:set X:=[set u|grassmann_val N u].
have hA:A!=set0:=structure_plane_nonempty N.
pose d:=@MetricSetDistance.value R [the metricType R of X] A hA.
have hd:is_metric_set_distance A d:=@MetricSetDistance.laws R [the metricType R of X] A hA.
pose C:set X:=[set v|NX v= 1 /\d v<=s].
have hCompact:compact C:=@approximate_normal_unit_directions_compact R n k N d s hd.
have hOutside v:C v ->~measure_approximate_tangent_cone
    (inner_norm_real_norm (@euclidean_inner_productP R n)) mu m a v.
  move=>[hv hDistance].
  exact:(@approximate_normal_unit_directions_nontangent R n m k mu a T N d s hT hN hd hs1 v hv hDistance).
have hHull:=@compact_nontangent_direction_hull_zero_density R (R_n R n) NX
  (inner_norm_real_norm (@euclidean_inner_productP R n)) mu m a C hMu hCompact hOutside.
apply:(@metric_restricted_density_zero_subset R [the metricType R of X] m mu
  (structure_cone N a +oo s) (positive_directional_hull a C) a hMu _ hHull).
move=>x hx.
have [hAngle _]:=((@structure_cone_specification R n k N a +oo s) d hd x).1 hx.
pose v:=(x-a)%R.
have hInvS:(0<=s^-1)%R by rewrite invr_ge0; exact:ltW hs.
have hVPositive:(0<NX v)%R.
  exact:le_lt_trans (mulr_ge0 hInvS (metric_set_distance_nonnegative hd v)) hAngle.
have hV:v!=0 by rewrite -(inner_norm_gt0 (@euclidean_inner_productP R n)).
pose w:=inner_normalize (@euclidean_inner_productP R n) v.
have hUnit:NX w= 1:=inner_normalize_norm _ hV.
have hdNorm:@is_metric_set_distance R
    (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n)))
    [set u|grassmann_val N u] d.
  constructor.
  - move=>y z hz; exact:(metric_set_distance_lower hd y hz).
  - move=>y t hLower; apply:(metric_set_distance_greatest hd)=>z hz.
    exact:hLower z hz.
have hSeminorm:=@subspace_distance_is_seminorm R (R_n R n) NX
  (inner_norm_real_norm (@euclidean_inner_productP R n)) (grassmann_val N) d hdNorm.
have hDistance:d w<=s.
  rewrite /w /inner_normalize (real_seminorm_scale hSeminorm) normrV;
    last by rewrite unitfE inner_norm_eq0.
  change (is_true (`|NX v|^-1*d v<=s)%R).
  rewrite (ger0_norm (ltW hVPositive)).
  exact:ltW (@cone_angle_unit_normalization R s (NX v) (d v) hs hVPositive hAngle).
change (exists (t:R) (y:R_n R n),0<t /\C y /\x=a+t *:y).
exists (NX v); exists w; split; first exact:hVPositive.
split; first by split.
rewrite /w (inner_normalizeK _ hV) /v addrC subrK.
by [].
Qed.
