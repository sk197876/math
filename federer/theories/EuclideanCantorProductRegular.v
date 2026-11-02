(** Federer (1969), 2.10.29, pp. 194–195: Borel regularity of the actual
    competing Euclidean product measure and measurability of the Cantor
    product. The factor Cantor sets are compact. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  RealMetricBackground EuclideanRealPlane EuclideanRealPlaneTopology EuclideanCantorProduct
  MeasureUP MeasureRestriction ProductMeasure MetricCartesianRectangleBounds PowerCantorProductMeasure
  MetricRealPowerMeasure MetricRealPowerClosedCovers BorelRegularMeasureUP BorelRegularRestriction
  TopologicalBorel ProductBorelRegularity ProductBorelRectangles MeasureCoordinateTransport
  ContinuousBorelPreimages StieltjesBorelRegularity MetricCartesianProductUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section ProductRegularity.
Variable R : realType.
Local Notation L := (real_line_metric R).
Local Notation E := (inner_metric_space (@euclidean_inner_productP R 2)).

(** Source for [euclidean_cantor_product_borel]: supporting
    Borel measurability of the actual compact
    Cantor product in 2.10.29, pp. 194–195.
    General compact factors suffice. *)
Lemma euclidean_cantor_product_borel (A B : set L) :
  compact A -> compact B -> borel_set (euclidean_cantor_product A B).
Proof.
move=> hA hB.
have hAB := borel_product_rectangle
  (closed_borel_set (compact_closed (@metric_hausdorff R [the metricType R of L]) hA))
  (closed_borel_set (compact_closed (@metric_hausdorff R [the metricType R of L]) hB)).
exact (@continuous_borel_preimage E (Topological.clone (L*L)%type _)
  (fun p=>(euclidean_real_plane_first p,euclidean_real_plane_second p))
  (@euclidean_real_plane_coordinates_continuous R) (A `*` B) hAB).
Qed.

(** Source for [euclidean_cantor_competing_product_borel_regular]: supporting
    Borel regularity of the competing measure
    in 2.10.29, pp. 194–195, from the
    actual compact restrictions and the Euclidean
    pairing homeomorphism. *)
Theorem euclidean_cantor_competing_product_borel_regular (c m : R) (hc : 0<=c) (A B : set L) :
  compact A -> compact B ->
  is_borel_regular_measure (@power_cantor_product_measure R [the metricType R of E]
    (@euclidean_real_plane_pair R) c m hc A B).
Proof.
move=> hA hB.
have hmu := @metric_real_power_measure_is_measure R [the metricType R of L] c m hc.
have hrmu := @metric_real_power_measure_borel_regular R [the metricType R of L] c m hc.
have hrestrict C : compact C -> is_borel_regular_measure (power_cantor_restricted_measure c m C).
  move=> hC; apply: (borel_regular_restrict_borel hmu hrmu).
  exact: closed_borel_set (compact_closed (@metric_hausdorff R [the metricType R of L]) hC).
have [V hV] := @real_line_countable_open_base_exists R.
have hprod := @product_measure_borel_regular R L L _ _
  (@power_cantor_restricted_is_measure R c m A hc) (@power_cantor_restricted_is_measure R c m B hc)
  V V hV hV (hrestrict A hA) (hrestrict B hB).
have hf : cancel (fun p : L*L=>euclidean_real_plane_pair p.1 p.2)
    (fun p=>(euclidean_real_plane_first p,euclidean_real_plane_second p)).
  move=> p; rewrite (metric_product_first_pair (@euclidean_real_plane_is_metric_product R))
    (metric_product_second_pair (@euclidean_real_plane_is_metric_product R)); exact (esym (surjective_pairing p)).
have hg : cancel (fun p=>(euclidean_real_plane_first p,euclidean_real_plane_second p))
    (fun p : L*L=>euclidean_real_plane_pair p.1 p.2).
  exact: metric_product_pair_coordinates (@euclidean_real_plane_is_metric_product R).
exact (@homeomorphic_pushforward_borel_regular R (Topological.clone (L*L)%type _) E _
  (product_measure_is_measure (@power_cantor_restricted_is_measure R c m A hc) (@power_cantor_restricted_is_measure R c m B hc))
  _ _ hf hg (@euclidean_real_plane_pair_continuous R) (@euclidean_real_plane_coordinates_continuous R) hprod).
Qed.
End ProductRegularity.
