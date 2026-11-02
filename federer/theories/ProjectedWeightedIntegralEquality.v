(** Federer (1969), 2.10.24, p. 188, final paragraph: the weighted-integral
    equality for the constructions 2.10.4(1) and 2.10.5(1), pp. 172–173.
    Apply the proved Borel-cost theorem and the actual weighted projection
    estimates; Euclidean separability discharges 2.10.8. Inputs are
    arbitrary nonnegative extended functions, without measurability or
    sigma-finite positive-support premises. The existing integer-degree
    interfaces include degree zero under their documented empty-product
    convention; all norm exponents at least one, including infinity, are
    retained. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureIntegralBounds
  EuclideanInnerProduct InnerMetric EuclideanMetricSeparability ProjectedVolumeGaugeUP ProjectedVolumeGauge
  ProjectionMeasure IntegralGeometricGauge IntegralGeometricMeasure IntegralGeometricCoverCosts
  WeightedMetricLimit BorelCoverCostUP ProjectedWeightedBorelCosts WeightedBorelIntegralEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [gross_weighted_integral_equality]: direct Gross
    application in the last paragraph of 2.10.24,
    p. 188, for the original Borel-generator construction
    2.10.4(1), p. 172. Every covering coefficient is
    finite real; f itself may be infinite and
    nonmeasurable. No support finiteness is added. *)
Theorem gross_weighted_integral_equality (R : realType) (n m : nat)
    (f : inner_metric_space (@euclidean_inner_productP R n) -> extended_real_line R) :
  (m<=n)%N -> (forall x, 0<=f x) ->
  weighted_metric_limit
    (fun j : @borel_metric_sets R (inner_metric_space (@euclidean_inner_productP R n))=>val j)
    (fun j=>projected_volume_gauge m (val j)) (@gross_measure R n m) f=
    measure_upper_integral (@gross_measure R n m) (partial_function_total f).
Proof.
move=> hmn hf; have [D [hD hden]] := euclidean_metric_separable R n.
exact: (@weighted_borel_integral_equality R (inner_metric_space (@euclidean_inner_productP R n))
  (@projected_volume_gauge R n m) (@projected_volume_gauge_borel_cover_cost R n m hmn)
  (@projected_volume_weighted_borel_cost R n m hmn) D f hD hden hf).
Qed.

(** Source for [integral_geometric_weighted_integral_equality]: direct
    integral-geometric application in the last paragraph
    of 2.10.24, p. 188, for 2.10.5(1),
    pp. 172–173. The actual projection probability,
    positive normalization and Borel generator family
    are preserved. All exponents at least one,
    including infinity, and all nonnegative extended
    inputs are allowed without measurability assumptions. *)
Theorem integral_geometric_weighted_integral_equality (R : realType) (n m : nat)
    (hmn : (m<=n)%N) (p : \bar R)
    (f : inner_metric_space (@euclidean_inner_productP R n) -> extended_real_line R) :
  1<=p -> (forall x, 0<=f x) ->
  weighted_metric_limit
    (fun j : @borel_metric_sets R (inner_metric_space (@euclidean_inner_productP R n))=>val j)
    (fun j=>@integral_geometric_gauge R n m hmn p (val j))
    (@integral_geometric_measure R n m hmn p) f=
    measure_upper_integral (@integral_geometric_measure R n m hmn p) (partial_function_total f).
Proof.
move=> hp hf; have [D [hD hden]] := euclidean_metric_separable R n.
exact: (@weighted_borel_integral_equality R (inner_metric_space (@euclidean_inner_productP R n))
  (@integral_geometric_gauge R n m hmn p) (@integral_geometric_gauge_borel_cover_cost R n m hmn p hp)
  (@integral_geometric_weighted_borel_cost R n m hmn p hp) D f hD hden hf).
Qed.
