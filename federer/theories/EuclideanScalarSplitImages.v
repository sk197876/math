(** Supporting Federer (1969), 3.2.45, p. 279: the existing
    scalar-coordinate product identification supplies actual image
    measures and compact scalar fibres for the Fubini argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanCoordinateSplit EuclideanHeadSectionIntegral EuclideanLebesgueDimensions EuclideanLebesgueHaar
  LebesgueScalarMeasure RealMetricBackground CompactScalarProductSections ProductSections
  MeasureUP MeasurePushforward PushforwardMeasurableSets TopologicalBorel BorelRegularMeasureUP
  CountablyMeasurableUP CountablyMeasurableSubsets CountablyMeasurableProduct ProductMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_scalar_split_image_mass]: the actual
    coordinate-product measure from Federer 2.6.5, p. 120,
    supporting 3.2.45, p. 279. It holds on every source set,
    without a measurability or finite-mass premise. *)
Lemma euclidean_scalar_split_image_mass (R : realType) m
    (S : set (inner_metric_space (@euclidean_inner_productP R m.+1))) :
  product_measure (euclidean_lebesgue_is_measure R m) (lebesgue_scalar_is_measure R)
    ((@euclidean_split R m) @` S) = euclidean_lebesgue_measure m.+1 S.
Proof.
rewrite -euclidean_head_split_measure /measure_pushforward.
congr (euclidean_lebesgue_measure _ _).
apply/seteqP; split=> x.
- move=> [y hy hEqual].
  have h := congr1 (@euclidean_join R m) hEqual.
  by rewrite !euclidean_splitK in h; rewrite -h.
- move=> hx; by exists x.
Qed.

(** Source for [euclidean_scalar_split_compact_countably_measurable]:
    compact linear images satisfy the countable-measurability premise
    of Fubini, 2.6.2(3), p. 115, in the supporting argument for
    Federer 3.2.45, p. 279. Compactness gives the Borel source;
    the existing Euclidean sigma-finiteness supplies countability. *)
Lemma euclidean_scalar_split_compact_countably_measurable (R : realType) m
    (S : set (inner_metric_space (@euclidean_inner_productP R m.+1))) :
  compact S ->
  measure_countably_measurable
    (product_measure (euclidean_lebesgue_is_measure R m) (lebesgue_scalar_is_measure R))
    ((@euclidean_split R m) @` S).
Proof.
move=> hS.
have hPre : (@euclidean_split R m) @^-1` ((@euclidean_split R m) @` S) = S.
  apply/seteqP; split=> x.
  - move=> [y hy hEqual].
    have h := congr1 (@euclidean_join R m) hEqual.
    by rewrite !euclidean_splitK in h; rewrite -h.
  - move=> hx; by exists x.
have hMeas : measure_measurable
    (product_measure (euclidean_lebesgue_is_measure R m) (lebesgue_scalar_is_measure R))
    ((@euclidean_split R m) @` S).
  rewrite -euclidean_head_split_measure.
  apply: pushforward_measurable_from_preimage.
  rewrite hPre.
  apply: (@borel_regular_borel_measurable R
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R m.+1)]
    (@euclidean_lebesgue_measure R m.+1) (euclidean_lebesgue_is_measure R m.+1)
    (euclidean_lebesgue_borel_regular R m.+1)).
  exact: closed_borel_set (compact_closed
    (@metric_hausdorff R [the metricType R of inner_metric_space (@euclidean_inner_productP R m.+1)]) hS).
apply: (measurable_subset_countably_measurable
  (product_measure_is_measure (euclidean_lebesgue_is_measure R m) (lebesgue_scalar_is_measure R))
  hMeas (subsetT _)).
exact: product_whole_countably_measurable (euclidean_lebesgue_countably_measurable R m)
  (lebesgue_scalar_countably_measurable R).
Qed.

(** Source for [euclidean_scalar_split_compact_fibre_finite]: every
    scalar fibre of an actual compact Euclidean image has finite
    length. This discharges a helper hypothesis in the expanded
    continuity proof of Federer 3.2.45, p. 279, by compact
    scalar sections and local finiteness from 2.7.16, p. 134. *)
Lemma euclidean_scalar_split_compact_fibre_finite (R : realType) m
    (S : set (inner_metric_space (@euclidean_inner_productP R m.+1))) :
  compact S -> forall y,
  lebesgue_scalar_measure (product_vertical_section ((@euclidean_split R m) @` S) y) < +oo.
Proof.
move=> hS y; apply: lebesgue_scalar_compact_finite.
apply: (@compact_scalar_product_section R
  [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] _ y).
- exact: metric_hausdorff.
- have hContinuous : continuous (@euclidean_split R m :
      inner_metric_space (@euclidean_inner_productP R m.+1) ->
      (inner_metric_space (@euclidean_inner_productP R m) * real_line_metric R)) :=
      @euclidean_split_continuous R m.
  exact: (@continuous_compact
    [the topologicalType of inner_metric_space (@euclidean_inner_productP R m.+1)]
    [the topologicalType of (inner_metric_space (@euclidean_inner_productP R m) * real_line_metric R)%type]
    (@euclidean_split R m) S (continuous_subspaceT hContinuous) hS).
Qed.
