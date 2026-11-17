(** Federer (1969), 2.10.45, printed p. 202, first displayed lower estimate
    for gamma(U), obtained from 2.10.27 and 2.10.35. For the measurable U
    needed by the final theorem, its section-mass function is the
    nonnegative constant H^k(V) times the characteristic of U. The
    corresponding integral gives the lower comparison, including infinite
    Lebesgue measure and zero second-factor mass. No measurability
    assumption on V is added. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealHausdorffMeasure RealHausdorffNormalisation
  RealHausdorffMeasureLaws RealHausdorffDegreeTransport RealPower RealPowerSuccessor
  RealPowerNaturalHausdorff MetricRealPowerCost RealPowerCoverVariants
  RealPowerCutoffFiniteCover MetricRealPowerMaps HausdorffRectangleLowerBound HausdorffProductSliceTranslation ExtendedRealOrderTopology EuclideanInnerProduct InnerMetric
  EuclideanLebesgueDimensions EuclideanBallVolume EuclideanHausdorffLebesgue EuclideanClosedBallCompact
  MetricCartesianProductUP MetricProductRectangles RealHausdorffProductSliceMeasure RealHausdorffProductSections
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

(** Source for [real_hausdorff_euclidean_rectangle_lower_bound]: supporting
    first displayed gamma lower bound in
    2.10.45, p. 202, in its equivalent
    multiplication form. The first factor is any
    Lebesgue measurable U; the final theorem has
    exactly this hypothesis. No finite-mass premise
    is needed for this lower bound alone. *)
Theorem real_hausdorff_euclidean_rectangle_lower_bound (R : realType) m (P Y : metricType R)
    (pair : inner_metric_space (@euclidean_inner_productP R m) -> Y -> P)
    first second (hp : is_metric_cartesian_product pair first second) (k : R) (hk : (0<=k)%R) U V :
  measure_measurable (@euclidean_lebesgue_measure R m) U ->
    euclidean_lebesgue_measure m U* @real_hausdorff_measure R Y k hk V<=
    (real_hausdorff_normalisation hk*real_hausdorff_normalisation (ler0n R m)/
      real_hausdorff_normalisation (addr_ge0 hk (ler0n R m)))%R%:E*real_hausdorff_product_slice_measure first second V (addr_ge0 hk (ler0n R m)) U.
Proof.
move=> hU.
pose E := inner_metric_space (@euclidean_inner_productP R m).
pose A := metric_product_rectangle first second U V.
pose s := @CharacteristicFunction.value R E U.
have hs : is_characteristic_function U s := @CharacteristicFunction.laws R E U.
have heH : @real_hausdorff_measure R E m%:R (ler0n R m)=euclidean_lebesgue_measure m.
  apply: funext=> B; rewrite real_hausdorff_measure_natural.
  exact: (euclidean_hausdorff_spherical_lebesgue B).1.
have hcond : real_metric_section_integral_condition pair A hk (ler0n R m).
  right; move=> a r hr; exact: euclidean_closed_metric_ball_compact.
have hh := @federer_2_10_27_real_hausdorff R P [the metricType R of E] Y pair first second hp A k m%:R hk (ler0n R m) hcond.
have heq : (fun x=>(@real_hausdorff_measure R Y k hk (metric_product_section pair A x) : extended_real_line R))=
    (fun x=>(@real_hausdorff_measure R Y k hk V*(s x)%:E : extended_real_line R)).
  apply: funext=> x; case: (pselect (U x))=> hx.
  - by rewrite /A (hausdorff_product_rectangle_section_inside hp V hx)
      (characteristic_on_set hs hx) mule1.
  - by rewrite /A (hausdorff_product_rectangle_section_outside hp V hx)
      (measure_empty (@real_hausdorff_measure_is_measure R Y k hk))
      (characteristic_off_set hs hx) mule0.
rewrite heq heH in hh.
have hi := @measure_nonnegative_extended_characteristic_integral R E
  (@euclidean_lebesgue_measure R m) (euclidean_lebesgue_is_measure R m) U s
  (@real_hausdorff_measure R Y k hk V) hs hU (measure_nonnegative (@real_hausdorff_measure_is_measure R Y k hk) V).
have hei := @measure_upper_integral_unique R E (@euclidean_lebesgue_measure R m) _ _ _
  (measure_upper_integral_specification _ _) hi.2.1.
by rewrite hei muleC in hh.
Qed.
