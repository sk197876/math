(** Federer (1969), 3.2.35, p. 272:
    repeated orthogonal projection averages retain
    the original intrinsic-volume coefficients. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric InnerConvex CoveringFamilyUP
  EuclideanProjectionSpace EuclideanProjectionMetric EuclideanProjectionComposition
  ProjectionCompositionProbability OrthogonalProjectionProbability ConvexProjectedVolumeContinuity
  ProjectedVolumeMeasurability ConvexIntrinsicVolumeIntegrals IntegralGeometricGauge ProjectionBeta
  PartialFunctionBasic ExtendedRealOrderTopology MeasurableFunctionUP MeasureUP MeasureIntegralUP
  MeasureIntegralUniqueness MeasurePushforward PushforwardTotalNonnegativeIntegral TopologicalProductMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [projection_composite_volume_fixed_left_integral]:
    the fixed-q repeated projection average in
    the final computation of Federer 3.2.35,
    p. 272. The previously proved actual
    composition pushforward law, 2.7.11(2), identifies
    the distribution. Actual convex-volume continuity
    supplies Borel measurability before the integral
    transport. The original source remains arbitrary
    nonempty bounded convex, without measurability;
    all natural projection dimensions are retained. *)
Theorem projection_composite_volume_fixed_left_integral (R:realType) n k m
    (hkn:(k<=n)%N) (hmk:(m<=k)%N)
    (C:orthogonal_projection_metric_space R k m*orthogonal_projection_metric_space R n k->
      orthogonal_projection_metric_space R n m)
    (S:set (inner_metric_space (@euclidean_inner_productP R n)))
    (q:orthogonal_projection_metric_space R k m):
  is_euclidean_projection_composition C ->S!=set0 ->is_inner_convex S ->metric_set_bounded S ->
  is_measure_integral (@orthogonal_projection_probability R n k hkn)
    (partial_function_total (fun p=>projected_volume_function S (C (q,p))))
    ((@projection_beta R n m (leq_trans hmk hkn) 1)%:E*
      @integral_geometric_gauge R n m (leq_trans hmk hkn) 1 S).
Proof.
move=>hC hNonempty hS hBound.
pose P:=orthogonal_projection_metric_space R n k.
pose theta:=@orthogonal_projection_probability R n k hkn.
have ht:=@theta_star_is_measure R n k hkn.
have hU:continuous (fun p:P=>C (q,p)).
  have hPair:continuous (fun p:P=>(q,p)).
    apply:topological_pair_continuous; first exact:cst_continuous.
    by move=>p; exact:cvg_id.
  move=>p; exact:continuous_comp (hPair p) (@euclidean_projection_composition_continuous R n k m C hC (q,p)).
have hMeasurable:=@convex_projected_volume_parameter_measurable R n m
  P theta (fun p=>C (q,p)) S ht
  (@theta_star_borel_regular R n k hkn) hU hNonempty hS hBound.
have [J [hI hPush]]:=@pushforward_total_nonnegative_integrals R P
  (orthogonal_projection_metric_space R n m) theta ht (fun p=>C (q,p))
  (projected_volume_function (m:=m) S) (fun p=>projected_volume_function_nonnegative S p) hMeasurable.
rewrite (@projection_composition_probability R n k m hkn hmk C hC q) in hPush.
have hValue:=measure_integral_unique hPush
  (@convex_intrinsic_volume_integral R n m (leq_trans hmk hkn) S hNonempty hS hBound).
by rewrite hValue in hI.
Qed.
