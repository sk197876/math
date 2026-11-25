(** Project regressions for the real-degree weighted-cover applications
    of Federer 2.10.24, pp. 187-188. The input is infinite at one point.
    Degree zero gives an infinite value; a positive nonintegral degree
    gives zero. Both use actual measures and finite real cover weights. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality
  reals constructive_ereal topology lra.
From Federer Require Import RealHausdorffWeightedSigmaFinite RealSphericalWeightedSigmaFinite
  RealHausdorffProperWeighted RealSphericalProperWeighted
  RealHausdorffMeasure RealHausdorffMeasureLaws RealHausdorffNormalisation
  RealPowerSingletonBound RealPower MetricRealPowerCost HausdorffLengthUP HausdorffMeasureUP
  HausdorffCountingMeasure SphericalCountingMeasure CountingMeasure
  CharacteristicFunctionUP CharacteristicFunctionSealed MeasureExtendedCharacteristicIntegral
  MeasureIntegralBounds MeasureIntegralUniqueness PartialFunctionBasic MeasureUP MeasureBasic
  BorelRegularMeasureUP TopologicalBorel FiniteExceptionalBorel WeightedMetricLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_zero_spherical_infinite_spike]: project regression
    for zero degree and infinite function values in Federer 2.10.24,
    pp. 187-188. An infinite singleton spike has infinite weighted
    spherical cutoff limit, since degree-zero measure counts the point. *)
Theorem real_zero_spherical_infinite_spike (R : realType) (X : metricType R)
    (hp : (0<=0 :> R)%R) (a : X) :
    weighted_metric_limit (fun j : @positive_closed_metric_balls R X => val j)
      (fun j => metric_real_diameter_cost (real_hausdorff_normalisation hp) 0%R (val j))
      (@real_spherical_measure R X 0%R hp)
      (fun x => +oo*(@CharacteristicFunction.value R X [set a] x)%:E)=+oo.
Proof.
pose mu := @real_spherical_measure R X 0%R hp.
pose s := @CharacteristicFunction.value R X [set a].
pose f x := +oo*(s x)%:E.
have hs := @CharacteristicFunction.laws R X [set a].
have he : mu=@counting_measure R X.
  apply: funext => B.
  rewrite /mu -[0%R]/(0%:R : R) real_spherical_measure_natural.
  exact: spherical_zero_counting_measure.
have hm : is_measure mu := @real_spherical_measure_is_measure R X 0%R hp.
have hmass : mu [set a] = 1.
  rewrite he -hausdorff_zero_counting_measure; exact: hausdorff_zero_singleton.
have hmeas : measure_measurable mu [set a].
  rewrite he; exact: counting_measure_measurable.
have hf x : 0<=f x.
  apply: mule_ge0; first exact: leey.
  exact: characteristic_extended_nonnegative hs x.
have hfinite n : mu ((fun _ : nat => [set a]) n)< +oo.
  rewrite hmass; exact: ltry.
have hcover : [set x | 0<f x] `<=` \bigcup_n (fun _ : nat => [set a]) n.
  move=> x hx; change (is_true (0<f x)) in hx.
  case: (pselect ([set a] x)) => hxa.
  - by exists 0%N.
  - have hz : f x=0 by rewrite /f /s (characteristic_off_set hs hxa) mule0.
    by rewrite hz ltxx in hx.
have h := @real_spherical_weighted_sigma_finite_equality R X 0%R hp
  f (fun _ => [set a]) hf hfinite hcover.
have hi := @measure_nonnegative_extended_characteristic_integral R X mu hm
  [set a] s +oo hs hmeas (leey 0).
rewrite hmass mule1 in hi.
have hu := @measure_upper_integral_unique R X mu _ _ +oo
  (measure_upper_integral_specification mu _) hi.2.1.
exact: eq_trans h hu.
Qed.

(** Source for [real_half_hausdorff_infinite_spike]: project regression
    for nonintegral degree and infinity times zero in Federer 2.10.24,
    pp. 187-188. An infinite spike on a singleton has zero weighted
    Hausdorff cutoff limit in degree one-half on every metric space. *)
Theorem real_half_hausdorff_infinite_spike (R : realType) (X : metricType R)
    (hp : (0<=(1/2 : R))%R) (a : X) :
    weighted_metric_limit (fun j : @nonempty_metric_sets R X => val j)
      (fun j => metric_real_diameter_cost (real_hausdorff_normalisation hp) (1/2 : R) (val j))
      (@real_hausdorff_measure R X (1/2 : R) hp)
      (fun x => +oo*(@CharacteristicFunction.value R X [set a] x)%:E)=0.
Proof.
pose mu := @real_hausdorff_measure R X (1/2 : R) hp.
pose s := @CharacteristicFunction.value R X [set a].
pose f x := +oo*(s x)%:E.
have hs := @CharacteristicFunction.laws R X [set a].
have hm : is_measure mu := @real_hausdorff_measure_is_measure R X (1/2 : R) hp.
have hpos : (0<(1/2 : R))%R by rewrite divr_gt0 // ltr0n.
have hb := @real_power_singleton_bound R X (real_hausdorff_normalisation hp)
  (1/2 : R) mu a (@real_hausdorff_measure_specification R X (1/2 : R) hp)
  (ltW (real_hausdorff_normalisation_positive hp)).
rewrite real_power_zero_base ?gt_eqF // mulr0 in hb.
have hmass : mu [set a]=0.
  apply/eqP; rewrite eq_le hb /=; exact: (@measure_nonnegative R X mu hm [set a]).
have hmeas : measure_measurable mu [set a].
  apply: (@borel_regular_borel_measurable R X mu hm
    (@real_hausdorff_measure_borel_regular R X (1/2 : R) hp)).
  exact: finite_metric_set_borel (finite_set1 a).
have hf x : 0<=f x.
  apply: mule_ge0; first exact: leey.
  exact: characteristic_extended_nonnegative hs x.
have hfinite n : mu ((fun _ : nat => [set a]) n)< +oo.
  rewrite hmass; exact: ltry.
have hcover : [set x | 0<f x] `<=` \bigcup_n (fun _ : nat => [set a]) n.
  move=> x hx; change (is_true (0<f x)) in hx.
  case: (pselect ([set a] x)) => hxa.
  - by exists 0%N.
  - have hz : f x=0 by rewrite /f /s (characteristic_off_set hs hxa) mule0.
    by rewrite hz ltxx in hx.
have h := @real_hausdorff_weighted_sigma_finite_equality R X (1/2 : R) hp
  f (fun _ => [set a]) hf hfinite hcover.
have hi := @measure_nonnegative_extended_characteristic_integral R X mu hm
  [set a] s +oo hs hmeas (leey 0).
rewrite hmass mule0 in hi.
have hu := @measure_upper_integral_unique R X mu _ _ 0
  (measure_upper_integral_specification mu _) hi.2.1.
exact: eq_trans h hu.
Qed.
