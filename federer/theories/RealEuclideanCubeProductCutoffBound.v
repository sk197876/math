(** Federer (1969), 2.10.45, printed p. 203: take the infimum over covers of
    the second factor in the displayed double-sum estimate. The target is
    still a size-cutoff approximation; its final supremum is taken only
    after removing the extra mesh margin. Source context:
    SquaredMetricProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets
  constructive_ereal topology lra.
From Federer Require Import RealHausdorffMeasure RealHausdorffNormalisation
  RealHausdorffMeasureLaws RealHausdorffDegreeTransport RealPower RealPowerSuccessor
  RealPowerNaturalHausdorff MetricRealPowerCost RealPowerCoverVariants
  RealPowerCutoffFiniteCover MetricRealPowerMaps HausdorffRectangleLowerBound HausdorffProductSliceTranslation ExtendedRealOrderTopology GrassmannAbbreviations EuclideanInnerProduct InnerMetric
  EuclideanBoxUP SquaredMetricProductUP MetricProductRectangles MetricDiameter
  HausdorffLengthUP HausdorffDiameterCost HausdorffMeasureUP HausdorffMeasure
  MetricScaleEnvelopeUP MetricScaleEnvelope MetricScaleCutoffCost CaratheodoryLimitUP
  MeasureUP MetricRectangleSliceMeasure ScaledMetricEnvelopeBound
  RealEuclideanProductCoefficient RealEuclideanCubeProductGeneratorBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_euclidean_cube_product_cutoff_margin_bound]: supporting
    covering-infimum step of 2.10.45, p. 203.
    The extra positive delta in (u+delta)^m remains
    explicit. No measurability or finite mass is yet
    required of the arbitrary second-factor set V. *)
Theorem real_euclidean_cube_product_cutoff_margin_bound (R : realType) (m : nat) (k : R) (hk : (0<=k)%R) (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R m) -> Y -> P)
    first second (hp : is_squared_metric_product pair first second)
    origin axis Q (u delta : R) (V : set Y) (Delta : \bar R) (nu : set P -> \bar R) :
  @is_euclidean_rectangular_box R m origin axis (fun _=>u) Q ->
  0<=u -> 0<delta -> ((Num.sqrt m.+1%:R*delta)%:E<=Delta)%E ->
  @is_metric_scale_envelope R P (@nonempty_metric_sets R P)
    (fun j=>val j) (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation (addr_ge0 hk (ler0n R m))) (k+m%:R)%R (val j)) Delta nu ->
    (nu (metric_product_rectangle first second Q V)<=
      (real_euclidean_product_upper_coefficient m hk*(u+delta)^+m)%:E*
        real_hausdorff_measure hk V)%E.
Proof.
move=> hQ hu hd hcap hn.
pose K := real_euclidean_product_upper_coefficient m hk*(u+delta)^+m.
have hK : 0<K.
  rewrite /K mulr_gt0 ?real_euclidean_product_upper_coefficient_positive //.
  apply: exprn_gt0; lra.
pose source := @metric_scale_envelope R Y (@nonempty_metric_sets R Y)
  (fun j=>val j) (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hk) k (val j)) (delta/2)%:E.
have hs := @metric_scale_envelope_specification R Y (@nonempty_metric_sets R Y)
  (fun j=>val j) (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hk) k (val j)) (delta/2)%:E.
have hnu : is_measure nu.
  apply: metric_scale_envelope_is_measure hn _=> j.
  exact: metric_real_diameter_cost_ge0 (ltW (real_hausdorff_normalisation_positive _)).
have hm := metric_rectangle_second_slice_is_measure first second Q hnu.
have hgen (j : nonempty_metric_sets Y)
    (hj : (extended_metric_diameter (val j)<=(delta/2)%:E)%E) :
    (nu (metric_product_rectangle first second Q (val j))<=
      K%:E*metric_real_diameter_cost (real_hausdorff_normalisation hk) k (val j))%E.
  apply: (@real_euclidean_cube_product_generator_bound R m k hk P Y pair first second hp
    origin axis Q u (delta/2) delta (val j) Delta nu hQ hu hd _ hj hcap hn).
  lra.
have hb := @measure_bounded_by_scaled_metric_envelope R Y (@nonempty_metric_sets R Y)
  (fun j=>val j) (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hk) k (val j)) (delta/2)%:E source
  (fun T=>nu (metric_product_rectangle first second Q T)) K hK hs hm hgen V.
have hpos : (0<(delta/2)%:E)%E by rewrite lte_fin; lra.
have hlim := caratheodory_limit_upper (@real_hausdorff_measure_specification R Y k hk) V hpos hs.
apply: le_trans hb _; apply: lee_wpmul2l hlim.
by rewrite lee_fin; exact: ltW hK.
Qed.
