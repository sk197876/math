(** Federer (1969), 2.10.45, printed p. 202: gamma(U)=H^(k+m)(U times V) is
    invariant under translations in the Euclidean factor. Coordinate
    recovery identifies the translated rectangle, and the already derived
    product isometry gives equality of its Hausdorff measure. The second
    factor and V remain arbitrary; no measurability, closedness or
    finite-mass assumption is needed for this intermediate fact. Source
    context: SquaredMetricProductUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric SquaredMetricProductUP SquaredMetricProductLaws
  MetricCartesianProductUP MetricProductRectangles EuclideanProductTranslation HausdorffProductSliceMeasure
  HausdorffMeasure HausdorffIsometricBijection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_product_translation_rectangle]: supporting
    identification of (a+U) times V with
    the translated U times V in 2.10.45,
    p. 202, from abstract product coordinate laws. *)
Lemma euclidean_product_translation_rectangle (R : realType) m (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R m) -> Y -> P)
    first second (hp : is_squared_metric_product pair first second) a U V :
  (euclidean_product_translation pair first second a) @` (metric_product_rectangle first second U V)=
    metric_product_rectangle first second ((fun x=>a+x) @` U) V.
Proof.
have hc := squared_metric_product_cartesian hp.
apply/seteqP; split.
- move=> p [q [hqU hqV] <-].
  rewrite /metric_product_rectangle /euclidean_product_translation /=
    (squared_product_first_pair_law hp) (squared_product_second_pair_law hp).
  split=> //; by exists (first q).
- move=> p [[x hx he] hy].
  exists (pair x (second p)).
  + rewrite /metric_product_rectangle /=
      (squared_product_first_pair_law hp) (squared_product_second_pair_law hp); by split.
  + by rewrite /euclidean_product_translation (squared_product_first_pair_law hp)
      (squared_product_second_pair_law hp) he (squared_product_recovery_law hp).
Qed.

(** Source for [hausdorff_product_slice_translation]: direct
    translation invariance of gamma asserted in
    2.10.45, p. 202. All natural
    degrees and arbitrary V are included. *)
Theorem hausdorff_product_slice_translation (R : realType) m (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R m) -> Y -> P)
    first second (hp : is_squared_metric_product pair first second) V d a U :
  hausdorff_product_slice_measure first second V d ((fun x=>a+x) @` U)=
    hausdorff_product_slice_measure first second V d U.
Proof.
rewrite /hausdorff_product_slice_measure -(euclidean_product_translation_rectangle hp).
have hc := @euclidean_product_translation_cancel R m P Y pair first second hp a.
have hci := @euclidean_product_translation_cancel R m P Y pair first second hp (-a).
rewrite opprK in hci.
exact (@hausdorff_bijective_isometry_invariance R P P
  (euclidean_product_translation pair first second a)
  (euclidean_product_translation pair first second (-a)) hc hci
  (@euclidean_product_translation_isometry R m P Y pair first second hp a) d _).
Qed.
