(** Federer (1969), 2.10.27, p. 191, final displayed Hausdorff product lower
    bound. Apply the first section inequality to the whole abstract product.
    Its sections are the whole second factor, and the integral of a
    nonnegative extended constant is its value times the measure of the
    first factor, including zero times infinity. it does not state this
    supporting calculation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealHausdorffMeasure RealHausdorffNormalisation
  RealHausdorffMeasureLaws MetricRealPowerCost RealPower RealPowerNaturalHausdorff
  MetricDiameterMaps RealHausdorffFibreCost RealHausdorffFibreCutoffs
  RealHausdorffProperWeighted RealHausdorffWeightedSigmaFinite ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MetricCartesianProductUP RealHausdorffProductSections HausdorffProductLowerBound LipschitzFunctionCompact EuclideanBallVolume
  HausdorffMeasure MeasureUP MeasureBasic MeasureSplit CharacteristicFunctionUP MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureExtendedCharacteristicIntegral CountablyMeasurableUP CountablyMeasurableSequences.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [federer_2_10_27_real_product_lower_bound]: direct
    final display of 2.10.27, p. 191.
    Retain the countably-H^m-measurable/proper alternative
    on the first factor. The Cartesian metric is
    abstract and both projections are nonexpanding.
    Both measure degrees are arbitrary nonnegative reals with the actual Gamma coefficient. *)
Theorem federer_2_10_27_real_product_lower_bound (R : realType) (P Y Z : metricType R)
    (pair : Y -> Z -> P) (first : P -> Y) (second : P -> Z)
    (hp : is_metric_cartesian_product pair first second) (k m : R) (hk : (0<=k)%R) (hm : (0<=m)%R) :
  (measure_countably_measurable (@real_hausdorff_measure R Y m hm) setT \/ metric_boundedly_compact Y) ->
  @real_hausdorff_measure R Y m hm setT* @real_hausdorff_measure R Z k hk setT<=
    (real_hausdorff_normalisation hk*real_hausdorff_normalisation hm/
      real_hausdorff_normalisation (addr_ge0 hk hm))%R%:E* @real_hausdorff_measure R P (k+m)%R (addr_ge0 hk hm) setT.
Proof.
move=> hcond.
have hsections y : metric_product_section pair setT y=setT by apply/seteqP; split=> z _.
have hsectioncond : real_metric_section_integral_condition pair setT hk hm.
  case: hcond=> [hc|hY]; last by right.
  have [B [hcover hB]] := (countably_measurable_sequence_iff (@real_hausdorff_measure_is_measure R Y m hm) setT).1 hc.
  left; exists B; split; first by move=> n; exact: (hB n).2.
  by move=> y _; rewrite -hcover.
have hh := @federer_2_10_27_real_hausdorff R P Y Z pair first second hp setT k m hk hm hsectioncond.
have heq : (fun y=>(@real_hausdorff_measure R Z k hk (metric_product_section pair setT y) : extended_real_line R))=
    (fun _ : Y=>(@real_hausdorff_measure R Z k hk setT : extended_real_line R)).
  apply: funext=> y; by rewrite hsections.
rewrite heq in hh.
have hi := @nonnegative_extended_constant_integral R Y (@real_hausdorff_measure R Y m hm)
  (@real_hausdorff_measure_is_measure R Y m hm) (@real_hausdorff_measure R Z k hk setT)
  (measure_nonnegative (@real_hausdorff_measure_is_measure R Z k hk) setT).
have he := @measure_upper_integral_unique R Y (@real_hausdorff_measure R Y m hm) _ _ _
  (measure_upper_integral_specification _ _) hi.2.1.
by rewrite he muleC in hh.
Qed.
