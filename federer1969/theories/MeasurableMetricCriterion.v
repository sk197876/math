(** Federer (1969), 2.3.2(8), p. 74: metric-valued measurability criterion,
    proved by distance to closed sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionPreimages PartialFunctionPostcomposition
  ExtendedRealOrderTopology MeasureUP MeasureSplit MeasureAlmostUP MeasurableFunctionUP
  MeasurableFunctionBorel MeasurableOrderRayVariants TopologicalBorel CountableOrderIntervals
  MeasurableSeparationUP MeasurableImageSeparation MeasurableLevelCriterion
  MetricSetDistanceUP MetricSetDistanceSealed MetricSetDistanceBasic MetricSetDistanceClosure
  MetricDistanceLevelSeparation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [image_separation_closed_preimage_measurable]: direct
    closed-preimage conclusion in Federer 2.3.2(8), p. 74.
    For a nonempty closed C, its inverse image is the zero-level
    preimage of distance to C; the empty case is handled separately. *)
Lemma image_separation_closed_preimage_measurable (R : realType) (X : choiceType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X Y) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  is_measure_image_separated mu f -> forall C, closed C ->
    measure_measurable mu (partial_function_preimage f C).
Proof.
move=> hdom hs C hC; case: (pselect (C !=set0))=> [hn|he].
- pose d := @MetricSetDistance.value R Y C hn.
  have hd := @MetricSetDistance.laws R Y C hn.
  pose g := partial_function_postcompose f (fun y => ((d y)%:E : extended_real_line R)).
  have hgdom : measure_almost_everywhere mu (partial_function_domain g).
    by rewrite /g /measure_almost_everywhere partial_function_postcompose_domain.
  have hgs : is_measure_level_separated mu g :=
    @image_separation_distance_level_separated R X Y mu f C d hd hs.
  have hgm := (proj2 (@measurable_extended_level_separation_iff R X mu hm g hgdom)) hgs.
  have hmzero : measure_measurable mu (partial_function_preimage g [set z | z <= (0 : R)%:E]).
    apply: (@measurable_function_borel_preimage R X (extended_real_line R) mu hm g hgm).
    apply: closed_borel_set; exact: order_closed_lower_ray_closed.
  have hlevel : [set y | (d y)%:E <= (0 : R)%:E] = C.
    apply/seteqP; split=> y.
    + move=> hy; apply: hC; apply: (proj1 (metric_set_distance_zero_closure hd y)).
      apply/eqP; rewrite eq_le (metric_set_distance_nonnegative hd y) andbT.
      by move: hy; rewrite /= lee_fin.
    + move=> hy; change ((d y)%:E <= (0 : R)%:E).
      have hz : d y = 0%R := @metric_set_distance_member R Y C d hd y hy.
      by rewrite hz.
  by move: hmzero; rewrite /g partial_function_postcompose_preimage hlevel.
- have hzero : C = set0 by apply/seteqP; split=> y // hy; apply: he; exists y.
  rewrite hzero partial_function_preimage_empty; exact: measure_measurable_empty hm.
Qed.

(** Source for [measurable_metric_image_separation_iff]: direct
    equivalence (8) in Federer 2.3.2, p. 74, for arbitrary
    metric targets, with explicit conull partial domain. Positive
    set distance is expressed by a positive uniform cross-distance bound. *)
Theorem measurable_metric_image_separation_iff (R : realType) (X : choiceType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (f : partial_function X Y) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  (is_measure_measurable_function mu f <-> is_measure_image_separated mu f).
Proof.
move=> hd; split; first exact: measurable_function_image_separated.
move=> hs; constructor=> // U hU.
have hC := @image_separation_closed_preimage_measurable R X Y mu hm f hd hs
  (~` U) (open_closedC hU).
have h := (proj1 (@measurable_partial_preimage_complement_iff R X Y mu hm f (~` U) hd)) hC.
by rewrite setCK in h.
Qed.
