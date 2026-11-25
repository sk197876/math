(** Federer (1969), 2.10.45, printed p. 202: gamma(U)=H^(k+m)(U times V) is
    invariant under translations in the Euclidean factor. Coordinate
    recovery identifies the translated rectangle, and the already derived
    product isometry gives equality of its Hausdorff measure. The second
    factor and V remain arbitrary; no measurability, closedness or
    finite-mass assumption is needed for this intermediate fact. Source
    context: SquaredMetricProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealHausdorffMeasure RealHausdorffNormalisation
  RealHausdorffMeasureLaws RealHausdorffDegreeTransport RealPower RealPowerSuccessor
  RealPowerNaturalHausdorff MetricRealPowerCost RealPowerCoverVariants
  RealPowerCutoffFiniteCover MetricRealPowerMaps HausdorffRectangleLowerBound HausdorffProductSliceTranslation EuclideanInnerProduct InnerMetric SquaredMetricProductUP SquaredMetricProductLaws
  MetricCartesianProductUP MetricProductRectangles EuclideanProductTranslation RealHausdorffProductSliceMeasure
  HausdorffMeasure HausdorffIsometricBijection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [real_hausdorff_product_slice_translation]: direct
    translation invariance of gamma asserted in
    2.10.45, p. 202. All natural
    degrees and arbitrary V are included. *)
Theorem real_hausdorff_product_slice_translation (R : realType) m (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R m) -> Y -> P)
    first second (hp : is_squared_metric_product pair first second) V (d : R) (hd : (0<=d)%R) a U :
  real_hausdorff_product_slice_measure first second V hd ((fun x=>a+x) @` U)=
    real_hausdorff_product_slice_measure first second V hd U.
Proof.
rewrite /real_hausdorff_product_slice_measure -(euclidean_product_translation_rectangle hp).
have hc := @euclidean_product_translation_cancel R m P Y pair first second hp a.
have hci := @euclidean_product_translation_cancel R m P Y pair first second hp (-a).
rewrite opprK in hci.
apply: (@metric_real_power_isometric_image R P P
  (real_hausdorff_normalisation hd) d
  (euclidean_product_translation pair first second a)
  (euclidean_product_translation pair first second (-a))
  (ltW (real_hausdorff_normalisation_positive hd)) hd hc).
- move=> x y; by rewrite (@euclidean_product_translation_isometry R m P Y pair first second hp a).
- move=> x y; by rewrite (@euclidean_product_translation_isometry R m P Y pair first second hp (-a)).
Qed.
