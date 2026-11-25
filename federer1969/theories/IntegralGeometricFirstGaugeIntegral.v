(** Federer (1969), 3.2.35, p. 271:
    the intrinsic volume is the actual
    projected-volume integral divided by beta_1,
    using the existing gauge of 2.10.5. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanProjectionMetric OrthogonalProjectionProbability
  ProjectedVolumeMeasurability IntegralGeometricGauge ProjectionBeta ProjectionIncidenceMeasure
  SuslinSetUP PartialFunctionBasic MeasureIntegralUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ereal_scope.

(** Source for [integral_geometric_first_gauge_integral]:
    direct defining average of zeta^m(S) in
    Federer 3.2.35, p. 271, retaining
    actual projected volumes, the existing sealed
    projection probability and its existing beta.
    This supporting assertion also permits degree
    zero and all Suslin sets, without boundedness
    or convexity. *)
Theorem integral_geometric_first_gauge_integral (R:realType) n m (hmn:(m<=n)%N)
    (S:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_suslin_set R S ->
  is_measure_integral (@orthogonal_projection_probability R n m hmn)
    (partial_function_total (projected_volume_function (m:=m) S))
    ((@projection_beta R n m hmn 1)%:E*@integral_geometric_gauge R n m hmn 1 S).
Proof.
move=>hS; rewrite (@integral_geometric_one_gauge_incidence R n m hmn S hS).
exact:projected_volume_incidence_integral hS.
Qed.
