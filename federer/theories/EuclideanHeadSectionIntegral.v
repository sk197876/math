(** Fubini supporting Federer (1969), 2.10.36, p. 198, the last volume
    estimate for the two-apex hull. Use the existing first-coordinate split
    into R^n times R and derive its actual measure and horizontal-section
    integral laws. Include the zero-dimensional base, whose measure is the
    established unit point mass. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerMetric
  EuclideanCoordinateSplit EuclideanOneCoordinate EuclideanLebesgue EuclideanLebesgueDimensions
  LebesgueScalarMeasure PointMassMeasure MeasureUP MeasureBasic MeasurePushforward
  MeasureBijectionUP MeasureBijectionCoordinateTransport SingletonProductMeasure BorelRegularMeasureUP
  ProductMeasure ProductSections ProductSetFubini CountablyMeasurableUP CountablyMeasurableSubsets
  CountablyMeasurableProduct PartialFunctionBasic MeasureIntegralUP PushforwardMeasurableSets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_head_split_measure]: supporting
    actual product-measure identity for the
    first-coordinate Fubini calculation implicit in
    2.10.36, p. 198. Positive
    dimensions use 2.6.5, pp. 119–120;
    an empty base uses unit point mass. *)
Lemma euclidean_head_split_measure (R : realType) (n : nat) :
  measure_pushforward (@euclidean_split R n) (@euclidean_lebesgue_measure R n.+1)=
    product_measure (euclidean_lebesgue_is_measure R n) (lebesgue_scalar_is_measure R).
Proof.
case: n=> [|n]; last first.
- have he : euclidean_lebesgue_is_measure R n.+1=positive_euclidean_lebesgue_is_measure R n := Prop_irrelevance _ _.
  rewrite he; exact: (@positive_euclidean_lebesgue_split_product R n).
have hp : euclidean_lebesgue_is_measure R 0=
    @point_mass_is_measure R (inner_metric_space (@euclidean_inner_productP R 0)) 0 := Prop_irrelevance _ _.
rewrite hp /euclidean_lebesgue_measure positive_euclidean_lebesgue_first measure_pushforward_composition.
have he : (@euclidean_split R 0) \o (@euclidean_one_embed R)=(fun t : R=>(0,t)).
  apply: funext=> t; rewrite /euclidean_split /=.
  rewrite (coordinate_zero (coordinate_tail (euclidean_one_embed t))).
  by rewrite /coordinate_head /euclidean_one_embed ffunE.
change (measure_pushforward ((@euclidean_split R 0) \o (@euclidean_one_embed R))
  (@lebesgue_scalar_measure R)=product_measure
    (@point_mass_is_measure R (inner_metric_space (@euclidean_inner_productP R 0)) 0)
    (lebesgue_scalar_is_measure R)).
rewrite he.
exact: measure_bijection_pushforward (@singleton_product_bijection R
  (inner_metric_space (@euclidean_inner_productP R 0)) R 0
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
  (@coordinate_zero R) (@borel_regular_is_regular R R^o (@lebesgue_scalar_measure R)
    (lebesgue_scalar_is_measure R) (lebesgue_scalar_borel_regular R))).
Qed.

(** Source for [euclidean_head_section_integral]: supporting
    horizontal-section integral used for the
    double-cone volume estimate in 2.10.36,
    p. 198. Every Lebesgue-measurable
    source is permitted; countable measurability
    follows from the proved Euclidean measure laws. *)
Theorem euclidean_head_section_integral (R : realType) (n : nat)
    (S : set (inner_metric_space (@euclidean_inner_productP R n.+1))) :
  measure_measurable (@euclidean_lebesgue_measure R n.+1) S ->
  is_measure_integral (@lebesgue_scalar_measure R)
    (partial_function_total (fun t : R=>euclidean_lebesgue_measure n
      (product_horizontal_section ((@euclidean_join R n) @^-1` S) t)))
    (euclidean_lebesgue_measure n.+1 S).
Proof.
move=> hS.
pose A := (@euclidean_join R n) @^-1` S.
have hp := @euclidean_head_split_measure R n.
have hA : measure_measurable
    (product_measure (euclidean_lebesgue_is_measure R n) (lebesgue_scalar_is_measure R)) A.
  rewrite -hp; apply: pushforward_measurable_from_preimage.
  have he : (@euclidean_split R n) @^-1` A=S.
    by apply/seteqP; split=> x; rewrite /A /= euclidean_splitK.
  by rewrite he.
have hc : measure_countably_measurable
    (product_measure (euclidean_lebesgue_is_measure R n) (lebesgue_scalar_is_measure R)) A.
  apply: (measurable_subset_countably_measurable
    (product_measure_is_measure (euclidean_lebesgue_is_measure R n) (lebesgue_scalar_is_measure R)) hA (subsetT A)).
  exact: product_whole_countably_measurable (euclidean_lebesgue_countably_measurable R n)
    (lebesgue_scalar_countably_measurable R).
have [_ [_ [_ hi]]] := product_set_fubini hc.
have he : product_measure (euclidean_lebesgue_is_measure R n) (lebesgue_scalar_is_measure R) A=
    euclidean_lebesgue_measure n.+1 S.
  rewrite -hp /measure_pushforward.
  by congr (euclidean_lebesgue_measure _ _); apply/seteqP; split=> x; rewrite /A /= euclidean_splitK.
by rewrite he in hi.
Qed.
