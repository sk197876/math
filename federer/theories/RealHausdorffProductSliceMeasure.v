(** Federer (1969), 2.10.45, printed p. 202, first proof paragraph:
    gamma(U)=H^(k+m)(U times V) is a measure on the Euclidean factor and
    every closed set is measurable for gamma. Express this derived measure
    as the image of a restricted Hausdorff measure. No regularity or
    measurability of V is imposed. The projection's nonexpansion suffices
    for Borel measurability, before the later squared-product translation
    argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealHausdorffMeasure RealHausdorffNormalisation
  RealHausdorffMeasureLaws RealHausdorffDegreeTransport RealPower RealPowerSuccessor
  RealPowerNaturalHausdorff MetricRealPowerCost RealPowerCoverVariants
  RealPowerCutoffFiniteCover MetricRealPowerMaps HausdorffRectangleLowerBound HausdorffProductSliceTranslation MetricCartesianProductUP MetricProductRectangles LipschitzUP
  NormMetricScaleContinuity HausdorffMeasure HausdorffClosedCoverAgreement
  MeasureUP MeasureRestriction MeasurePushforward PushforwardMeasurableSets
  TopologicalBorel ContinuousBorelPreimages BorelRegularMeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_hausdorff_product_slice_measure]: direct
    abbreviation gamma(U)=H^(k+m)(U times V)
    in the proof of 2.10.45, p. 202.
    The later theorem sets d=k+m; the definition
    and elementary measure laws permit any nonnegative real degree. *)
Definition real_hausdorff_product_slice_measure (R : realType) (P X Y : metricType R)
    (first : P -> X) (second : P -> Y) (V : set Y) (d : R) (hd : (0<=d)%R) (U : set X) :=
  @real_hausdorff_measure R P d hd (metric_product_rectangle first second U V).

(** Source for [real_hausdorff_product_slice_pushforward]: supporting
    image-of-restriction identity for gamma in
    2.10.45, p. 202, using the definitions
    of restriction and image measure in 2.1.2,
    p. 54. This does not require V measurable. *)
Lemma real_hausdorff_product_slice_pushforward (R : realType) (P X Y : metricType R)
    (first : P -> X) (second : P -> Y) (V : set Y) (d : R) (hd : (0<=d)%R) :
  real_hausdorff_product_slice_measure first second V hd=
    measure_pushforward first (measure_restrict (@real_hausdorff_measure R P d hd) (second @^-1` V)).
Proof.
by apply: funext=> U; rewrite /real_hausdorff_product_slice_measure /metric_product_rectangle
  /measure_pushforward /measure_restrict setIC.
Qed.

(** Source for [real_hausdorff_product_slice_is_measure]: direct
    gamma measures R^m assertion in 2.10.45,
    p. 202, before Euclidean specialisation. No
    finiteness or product-metric hypothesis is needed
    for this measure assertion alone. *)
Theorem real_hausdorff_product_slice_is_measure (R : realType) (P X Y : metricType R)
    (first : P -> X) (second : P -> Y) (V : set Y) (d : R) (hd : (0<=d)%R) :
  is_measure (real_hausdorff_product_slice_measure first second V hd).
Proof.
rewrite real_hausdorff_product_slice_pushforward.
exact: measure_pushforward_is_measure (measure_restrict_is_measure (@real_hausdorff_measure_is_measure R P d hd) _).
Qed.

(** Source for [real_hausdorff_product_slice_borel_measurable]: supporting
    Borel-set strengthening of the closed-set claim
    in 2.10.45, p. 202. The first
    projection is nonexpanding, so its Borel
    preimages are Hausdorff measurable; restricting
    by an arbitrary V preserves that measurability. *)
Theorem real_hausdorff_product_slice_borel_measurable (R : realType) (P X Y : metricType R)
    (pair : X -> Y -> P) first second (hp : is_metric_cartesian_product pair first second)
    (V : set Y) (d : R) (hd : (0<=d)%R) U :
  borel_set U -> measure_measurable (real_hausdorff_product_slice_measure first second V hd) U.
Proof.
move=> hU; rewrite real_hausdorff_product_slice_pushforward.
apply: pushforward_measurable_from_preimage; apply: measure_restrict_measurable.
apply: (borel_regular_borel_measurable (@real_hausdorff_measure_is_measure R P d hd)
  (@real_hausdorff_measure_borel_regular R P d hd)).
have hb := metric_product_first_nonexpanding hp.
have hc : continuous first.
  apply: (@metric_fixed_lipschitz_continuous R P X first 1%R hb.1)=> p q.
  exact: hb.2 p q I I.
exact (@continuous_borel_preimage P X first hc U hU).
Qed.
