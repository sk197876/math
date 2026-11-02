(** Federer (1969), 2.10.35, p. 197: both integral-geometric measures equal
    Lebesgue measure in the ambient dimension, for every exponent
    1<=t<=infinity. Their actual gauges equal projected volume, so the
    existing abstract covering uniqueness identifies I_t with Gross and Q_t
    with convex Caratheodory measure. No equality of different covering
    families is assumed. Source context: FullDimensionIntegralGauge.v and
    EuclideanConvexProjectionLebesgue.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  IntegralGeometricGauge IntegralGeometricMeasureUP IntegralGeometricMeasure
  FullDimensionIntegralGauge FullDimensionProjectedVolume ProjectedVolumeGauge
  ProjectionMeasureUP ProjectionMeasure BorelCoverCostUP CaratheodoryLimitUP CaratheodoryLimitUniqueness
  EuclideanExteriorLebesgue EuclideanConvexProjectionLebesgue.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.

(** Source for [euclidean_integral_geometric_lebesgue]: direct
    I_t^n=L^n equality of 2.10.35,
    p. 197. Equal generator costs
    identify the two Borel-family constructions,
    with arbitrary targets and infinite masses. *)
Theorem euclidean_integral_geometric_lebesgue (R : realType) (n : nat)
    (hnn : (n<=n)%N) (t : \bar R) :
  (1<=t)%E -> forall A,
    @integral_geometric_measure R n n hnn t A=euclidean_lebesgue_measure n A.
Proof.
move=> ht A.
have hc : (fun j : @borel_metric_sets R (inner_metric_space (@euclidean_inner_productP R n))=>
    @integral_geometric_gauge R n n hnn t (val j))=
    (fun j : @borel_metric_sets R (inner_metric_space (@euclidean_inner_productP R n))=>projected_volume_gauge n (val j)).
  by apply: funext=> j; rewrite (@equal_dimension_integral_geometric_gauge R n hnn t (val j) ht) equal_dimension_projected_volume_gauge.
have hi := @integral_geometric_measure_specification R n n hnn t.
rewrite /is_integral_geometric_measure hc in hi.
have he := caratheodory_limit_unique hi (gross_measure_specification R n n) A.
by rewrite euclidean_gross_measure_lebesgue in he.
Qed.

(** Source for [euclidean_convex_integral_geometric_lebesgue]: direct
    Q_t^n=L^n equality of 2.10.35,
    p. 197. Equal generator costs
    identify the original open convex constructions;
    their closed-cover alternatives have already
    been proved independently in 2.10.4–2.10.5. *)
Theorem euclidean_convex_integral_geometric_lebesgue (R : realType) (n : nat)
    (hnn : (n<=n)%N) (t : \bar R) :
  (1<=t)%E -> forall A,
    @convex_integral_geometric_measure R n n hnn t A=euclidean_lebesgue_measure n A.
Proof.
move=> ht A.
have hc : (fun j : open_convex_euclidean_sets R n=>@integral_geometric_gauge R n n hnn t (val j))=
    (fun j : open_convex_euclidean_sets R n=>projected_volume_gauge n (val j)).
  by apply: funext=> j; rewrite (@equal_dimension_integral_geometric_gauge R n hnn t (val j) ht) equal_dimension_projected_volume_gauge.
have hq := @convex_integral_geometric_measure_specification R n n hnn t.
rewrite /is_convex_integral_geometric_measure hc in hq.
have he := caratheodory_limit_unique hq (caratheodory_projection_measure_specification R n n) A.
by rewrite euclidean_convex_projection_lebesgue in he.
Qed.
