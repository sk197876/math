(** Federer (1969), 3.3.19, pp. 302–306:
    concrete original-object regression statements. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations GrassmannSubspaces EuclideanInnerProduct InnerMetric
  MetricClosedBalls MetricDensities MeasureRestriction HausdorffMeasure IntegralGeometricMeasure
  ProjectionMeasure ProjectionBeta EuclideanProjectionSpace EuclideanLebesgueDimensions
  CircularTrigonometrySealed CircularUnitVectors StructureCone.
From Federer Require Import CircularDiscActualCapCounterexample.
From Federer Require Import CircularDiscExample.
From Federer Require Import CircularDiscLimitMembership.
From Federer Require Import CircularDiscPieceConvexMass.
From Federer Require Import CircularDiscPositiveChildCounts.
From Federer Require Import CircularDiscTreeMinimum.
From Federer Require Import FiniteCyclicRetractionBudget.
From Federer Require Import PlanarRadialRetractionOptimal.
From Federer Require Import CircularDiscTreeSealed.
From Federer Require Import CircularDiscLimitSealed.
From Federer Require Import CircularDiscFixedBoundaryPoint.
From Federer Require Import CircularDiscCaps.
From Federer Require Import FactorialDiscScalesSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [circular_example_positive_H_and_Q_zero_Gross]:
    actual H1(A)=2, Q1(A)=pi and Gross(A)=0,
    the contrasting measure values of 3.3.19, pp. 304–306. *)
Example circular_example_positive_H_and_Q_zero_Gross (R:realType):
  let A:=@CircularDiscLimit.value R in
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 1 A=(2:R)%:E /\
  @convex_integral_geometric_measure R 2 1 (leqnSn 1) 1 A=(@CircularTrigonometry.half_period R)%:E /\
  @gross_measure R 2 1 A=0%E.
Proof.
move=>A;have h:=federer_3_3_19 R.
split;first exact:h.2.2.1.
split;first exact:h.2.2.2.2.1.
exact:h.2.2.2.2.2.2.2.2.1.
Qed.

(** Source for [circular_example_every_original_projection_null]:
    every original orthogonal line projection of actual A
    has outer length zero, 3.3.19, p. 306. *)
Example circular_example_every_original_projection_null (R:realType)
    (p:euclidean_projection_space R 2 1):
  euclidean_lebesgue_measure 1 (euclidean_projection_linear p @` @CircularDiscLimit.value R)=0%E.
Proof. exact:(federer_3_3_19 R).2.2.2.2.2.2.2.1. Qed.

(** Source for [circular_example_boundary_density_half]: the
    actual original boundary endpoint exp(0i) has upper
    density exactly one half. It is retained in the
    final density assertion of 3.3.19, p. 306. *)
Example circular_example_boundary_density_half (R:realType):
  let E:=inner_metric_space (@euclidean_inner_productP R 2) in
  upper_metric_density 1 (measure_restrict (@hausdorff_measure R [the metricType R of E] 1)
    (@CircularDiscLimit.value R)) (@circular_unit_vector R 0)=((1:R)/2)%:E.
Proof.
move=>E;apply:(federer_3_3_19 R).2.2.2.2.2.2.2.2.2.
exact:(@circular_disc_fixed_boundary_point_in_limit R (@CircularDiscTree.centres R)
  (@CircularDiscTree.laws R) (@CircularDiscLimit.value R) (@CircularDiscLimit.laws R)).
Qed.

(** Source for [circular_example_actual_parent_strict_radius_failure]:
    proved local correction to the auxiliary inclusion
    in 3.3.19, p. 305, at every actual positive
    parent level of the original example. A closed-cap
    point lies exactly at the excluded radius rho_j.
    The smaller-aperture proof preserves the numbered theorem. *)
Example circular_example_actual_parent_strict_radius_failure (R:realType) j:(1<=j)%N ->
  let E:=inner_metric_space (@euclidean_inner_productP R 2) in
  let rho:=@FactorialDiscScales.radius R in
  let pi:=@CircularTrigonometry.half_period R in
  exists z x:E,z \in @CircularDiscTree.centres R j /\
    @CircularDiscLimit.value R (@circular_unit_vector R 0) /\
    metric_closed_ball z (rho j) (@circular_unit_vector R 0) /\
    circular_disc_cap z (rho j) (@circular_unit_vector R (pi/6)) (pi/6) x /\
    @euclidean_inner_product R 2 (x-z) (@circular_unit_vector R 0)<rho j*(1-2/(j+4)%:R) /\
    (forall b:R,@CircularTrigonometry.cosine R b= 1-2/(j+4)%:R ->
      ~circular_disc_cap z (rho j) (@circular_unit_vector R 0) b x) /\
    forall V:G (R_n R 2) 1,~structure_cone V (@circular_unit_vector R 0) (rho j)%:E (1/2) x.
Proof.
move=>hj E rho pi;exact:(@circular_disc_actual_cap_counterexample R (@CircularDiscTree.centres R)
  (@CircularDiscTree.laws R) (@CircularDiscLimit.value R) (@CircularDiscLimit.laws R) j hj).
Qed.
