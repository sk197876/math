(** Federer (1969), 2.10.35, printed p. 197: equality of Lebesgue,
    spherical, Hausdorff, exterior-diameter, convex integral-geometric,
    integral-geometric and Gross measures on R^n. Collect the independently
    proved equalities of the actual measures. Source context and individual
    arguments are documented in EuclideanHausdorffLebesgue.v,
    EuclideanExteriorLebesgue.v and EuclideanIntegralGeometricLebesgue.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  HausdorffMeasure ExteriorMeasure ProjectionMeasure IntegralGeometricMeasure
  EuclideanHausdorffLebesgue EuclideanExteriorLebesgue EuclideanIntegralGeometricLebesgue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [federer_2_10_35]: direct full
    seven-measure equality of 2.10.35,
    p. 197, recorded by equating
    each of the other six actual
    measures to L^n. All targets and
    every 1<=t<=infinity are included; the
    supporting natural-degree interface retains dimension zero. *)
Theorem federer_2_10_35 (R : realType) (n : nat) (hnn : (n<=n)%N) (t : \bar R) :
  (1<=t)%E -> forall A : set (inner_metric_space (@euclidean_inner_productP R n)),
  @spherical_measure R (inner_metric_space (@euclidean_inner_productP R n)) n A=euclidean_lebesgue_measure n A /\
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) n A=euclidean_lebesgue_measure n A /\
  @exterior_diameter_measure R n n A=euclidean_lebesgue_measure n A /\
  @convex_integral_geometric_measure R n n hnn t A=euclidean_lebesgue_measure n A /\
  @integral_geometric_measure R n n hnn t A=euclidean_lebesgue_measure n A /\
  @gross_measure R n n A=euclidean_lebesgue_measure n A.
Proof.
move=> ht A; have [hH hS] := euclidean_hausdorff_spherical_lebesgue A.
split=> //; split=> //; split; first exact: euclidean_exterior_measure_lebesgue.
split; first exact: (@euclidean_convex_integral_geometric_lebesgue R n hnn t ht A).
split; [exact: (@euclidean_integral_geometric_lebesgue R n hnn t ht A)|exact: euclidean_gross_measure_lebesgue].
Qed.
