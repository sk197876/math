(** Federer (1969), 2.10.27, p. 191, final displayed Hausdorff product lower
    bound. Apply the first section inequality to the whole abstract product.
    Its sections are the whole second factor, and the integral of a
    nonnegative extended constant is its value times the measure of the
    first factor, including zero times infinity. it does not state this
    supporting calculation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionUP PartialFunctionBasic
  MetricCartesianProductUP HausdorffProductSections LipschitzFunctionCompact EuclideanBallVolume
  HausdorffMeasure MeasureUP MeasureBasic MeasureSplit CharacteristicFunctionUP MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureExtendedCharacteristicIntegral CountablyMeasurableUP CountablyMeasurableSequences.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_extended_constant_integral]: supporting
    constant-integrand calculation for the last display
    in 2.10.27, p. 191, from the characteristic
    integral laws of 2.4.5, p. 84. Infinite
    constants on null whole spaces still give zero. *)
Lemma nonnegative_extended_constant_integral (R : realType) (Y : choiceType)
    (mu : set Y -> \bar R) (hm : is_measure mu) (c : \bar R) :
  0<=c -> is_measure_integral mu (partial_function_total (fun _ : Y=>(c : extended_real_line R))) (c*mu setT).
Proof.
move=> hc.
have hs : is_characteristic_function setT (fun _ : Y=>(1%R : R)).
  split; first by move=> x _.
  by move=> x hx; exfalso; exact: hx Logic.I.
have hi := @measure_nonnegative_extended_characteristic_integral R Y mu hm setT (fun _=>(1%R : R)) c
  hs (measure_measurable_whole hm) hc.
have heq : (fun _ : Y=>(c*(1%R : R)%:E : extended_real_line R))=(fun _ : Y=>(c : extended_real_line R)).
  apply: funext=> x; exact: mule1.
by rewrite heq in hi.
Qed.

(** Source for [federer_2_10_27_product_lower_bound]: direct
    final display of 2.10.27, p. 191.
    Retain the countably-H^m-measurable/proper alternative
    on the first factor. The Cartesian metric is
    abstract and both projections are nonexpanding.
    All dimensions here are natural numbers. *)
Theorem federer_2_10_27_product_lower_bound (R : realType) (P Y Z : metricType R)
    (pair : Y -> Z -> P) (first : P -> Y) (second : P -> Z)
    (hp : is_metric_cartesian_product pair first second) k m :
  (measure_countably_measurable (@hausdorff_measure R Y m) setT \/ metric_boundedly_compact Y) ->
  @hausdorff_measure R Y m setT* @hausdorff_measure R Z k setT<=
    (euclidean_unit_ball_volume R k*euclidean_unit_ball_volume R m/
      euclidean_unit_ball_volume R (k+m))%R%:E* @hausdorff_measure R P (k+m) setT.
Proof.
move=> hcond.
have hsections y : metric_product_section pair setT y=setT by apply/seteqP; split=> z _.
have hsectioncond : metric_section_integral_condition pair setT k m.
  case: hcond=> [hc|hY]; last by right.
  have [B [hcover hB]] := (countably_measurable_sequence_iff (@hausdorff_measure_is_measure R Y m) setT).1 hc.
  left; exists B; split; first by move=> n; exact: (hB n).2.
  by move=> y _; rewrite -hcover.
have hh := @federer_2_10_27_hausdorff R P Y Z pair first second hp setT k m hsectioncond.
have heq : (fun y=>(@hausdorff_measure R Z k (metric_product_section pair setT y) : extended_real_line R))=
    (fun _ : Y=>(@hausdorff_measure R Z k setT : extended_real_line R)).
  apply: funext=> y; by rewrite hsections.
rewrite heq in hh.
have hi := @nonnegative_extended_constant_integral R Y (@hausdorff_measure R Y m)
  (@hausdorff_measure_is_measure R Y m) (@hausdorff_measure R Z k setT)
  (measure_nonnegative (@hausdorff_measure_is_measure R Z k) setT).
have he := @measure_upper_integral_unique R Y (@hausdorff_measure R Y m) _ _ _
  (measure_upper_integral_specification _ _) hi.2.1.
by rewrite he muleC in hh.
Qed.
