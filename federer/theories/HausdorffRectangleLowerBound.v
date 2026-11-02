(** Federer (1969), 2.10.45, printed p. 202, first displayed lower estimate
    for gamma(U), obtained from 2.10.27 and 2.10.35. For the measurable U
    needed by the final theorem, its section-mass function is the
    nonnegative constant H^k(V) times the characteristic of U. The
    corresponding integral gives the lower comparison, including infinite
    Lebesgue measure and zero second-factor mass. No measurability
    assumption on V is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanBallVolume EuclideanHausdorffLebesgue EuclideanClosedBallCompact
  MetricCartesianProductUP MetricProductRectangles HausdorffProductSliceMeasure HausdorffProductSections
  HausdorffMeasure MeasureUP MeasureBasic CharacteristicFunctionUP CharacteristicFunctionSealed
  PartialFunctionUP PartialFunctionBasic MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureExtendedCharacteristicIntegral LipschitzFunctionCompact.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [hausdorff_product_rectangle_section_inside]: supporting
    constant section V above x in U
    for the lower estimate in 2.10.45,
    p. 202. *)
Lemma hausdorff_product_rectangle_section_inside (R : realType) (P X Y : metricType R)
    (pair : X -> Y -> P) first second (hp : is_metric_cartesian_product pair first second) U V x :
  U x -> metric_product_section pair (metric_product_rectangle first second U V) x=V.
Proof.
move=> hx; apply/seteqP; split=> y.
- by rewrite /metric_product_section /metric_product_rectangle /=
    (metric_product_first_pair hp) (metric_product_second_pair hp)=> -[_ hy].
- rewrite /metric_product_section /metric_product_rectangle /=
    (metric_product_first_pair hp) (metric_product_second_pair hp); by split.
Qed.

(** Source for [hausdorff_product_rectangle_section_outside]: supporting
    empty section above x outside U in
    the lower estimate of 2.10.45, p. 202. *)
Lemma hausdorff_product_rectangle_section_outside (R : realType) (P X Y : metricType R)
    (pair : X -> Y -> P) first second (hp : is_metric_cartesian_product pair first second) U V x :
  ~ U x -> metric_product_section pair (metric_product_rectangle first second U V) x=set0.
Proof.
move=> hx; apply/seteqP; split=> y; last by [].
rewrite /metric_product_section /metric_product_rectangle /=
  (metric_product_first_pair hp) (metric_product_second_pair hp)=> -[hu _].
exact: hx hu.
Qed.

(** Source for [hausdorff_euclidean_rectangle_lower_bound]: supporting
    first displayed gamma lower bound in
    2.10.45, p. 202, in its equivalent
    multiplication form. The first factor is any
    Lebesgue measurable U; the final theorem has
    exactly this hypothesis. No finite-mass premise
    is needed for this lower bound alone. *)
Theorem hausdorff_euclidean_rectangle_lower_bound (R : realType) m (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R m) -> Y -> P)
    first second (hp : is_metric_cartesian_product pair first second) k U V :
  measure_measurable (@euclidean_lebesgue_measure R m) U ->
    euclidean_lebesgue_measure m U* @hausdorff_measure R Y k V<=
    (euclidean_unit_ball_volume R k*euclidean_unit_ball_volume R m/
      euclidean_unit_ball_volume R (k+m))%R%:E*hausdorff_product_slice_measure first second V (k+m) U.
Proof.
move=> hU.
pose E := inner_metric_space (@euclidean_inner_productP R m).
pose A := metric_product_rectangle first second U V.
pose s := @CharacteristicFunction.value R E U.
have hs : is_characteristic_function U s := @CharacteristicFunction.laws R E U.
have heH : @hausdorff_measure R E m=euclidean_lebesgue_measure m.
  apply: funext=> B; exact: (euclidean_hausdorff_spherical_lebesgue B).1.
have hcond : metric_section_integral_condition pair A k m.
  right; move=> a r hr; exact: euclidean_closed_metric_ball_compact.
have hh := @federer_2_10_27_hausdorff R P [the metricType R of E] Y pair first second hp A k m hcond.
have heq : (fun x=>(@hausdorff_measure R Y k (metric_product_section pair A x) : extended_real_line R))=
    (fun x=>(@hausdorff_measure R Y k V*(s x)%:E : extended_real_line R)).
  apply: funext=> x; case: (pselect (U x))=> hx.
  - by rewrite /A (hausdorff_product_rectangle_section_inside hp V hx)
      (characteristic_on_set hs hx) mule1.
  - by rewrite /A (hausdorff_product_rectangle_section_outside hp V hx)
      (measure_empty (@hausdorff_measure_is_measure R Y k))
      (characteristic_off_set hs hx) mule0.
rewrite heq heH in hh.
have hi := @measure_nonnegative_extended_characteristic_integral R E
  (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m) U s
  (@hausdorff_measure R Y k V) hs hU (measure_nonnegative (@hausdorff_measure_is_measure R Y k) V).
have hei := @measure_upper_integral_unique R E (@euclidean_lebesgue_measure R m) _ _ _
  (measure_upper_integral_specification _ _) hi.2.1.
by rewrite hei muleC in hh.
Qed.
