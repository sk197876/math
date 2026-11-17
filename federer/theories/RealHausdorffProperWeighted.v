(** Federer (1969), 2.10.24, p. 188: real-degree Hausdorff weighted-integral
    equality on boundedly compact metric spaces, without a
    sigma-finite-support assumption. At finite cutoffs the compact-generator
    reduction supplies actual continuity below from 2.10.22. The weak-level
    estimate then gives finite measures of positive levels, and the proved
    Hausdorff sigma-finite equality applies. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealHausdorffNormalisation RealHausdorffMeasure RealHausdorffMeasureLaws RealPowerCoverVariants MetricRealPowerCost
  RealHausdorffEnlargement RealSphericalEnlargement ExtendedRealOrderTopology PartialFunctionBasic MeasureIntegralBounds
  MetricDiameterUP MetricDiameter HausdorffLengthUP HausdorffMeasure HausdorffDiameterCost
  HausdorffPowerCostLaws RealPowerCompactCost RealPowerCompactCutoff RealPowerCompactLimit CompactSetDistanceProfile
  CompactCostContinuityBelow LipschitzFunctionCompact IncreasingProjectionLoss MetricScaleEnvelopeUP MetricScaleEnvelope
  ClosedHausdorffEnlargementUP HausdorffGeneratorEnlargement HausdorffCompactCost HausdorffCompactScaleAgreement WeightedMetricLimit
  WeightedMetricLimitLaws WeightedLimitLevelBound WeightedUpperIntegralBound RealHausdorffWeightedSigmaFinite ReciprocalSequenceLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [real_bounded_hausdorff_generator_cost_finite]: supporting
    finite gauge on the eligible bounded generators of
    2.10.24, p. 188. Unbounded generators outside
    a finite cutoff may retain infinite cost. *)
Lemma real_bounded_hausdorff_generator_cost_finite (R : realType) (X : metricType R) (p : R) (hp : (0<=p)%R) (S : set X) :
  extended_metric_diameter S< +oo -> metric_real_diameter_cost (real_hausdorff_normalisation hp) p S< +oo.
Proof.
move=> hf; have hn := metric_diameter_nonnegative (extended_metric_diameter_specification S).
have hfin : extended_metric_diameter S \is a fin_num by rewrite (ge0_fin_numE hn).
have he := fineK hfin.
rewrite /metric_real_diameter_cost -he metric_real_power_cost_finite; exact: ltry.
Qed.

(** Source for [real_hausdorff_finite_scale_continuity]: supporting
    actual continuity-below input for the Hausdorff
    application of 2.10.24, p. 188. It follows
    from exact compact-cover agreement at each positive
    finite cutoff and the checked theorem 2.10.22. *)
Theorem real_hausdorff_finite_scale_continuity (R : realType) (X : metricType R) (p : R) (hp : (0<=p)%R)
    (d : R) (nu : set X -> \bar R) :
  metric_boundedly_compact X -> (0<d)%R ->
  is_metric_scale_envelope (fun j : @nonempty_metric_sets R X=>val j)
    (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hp) p (val j)) d%:E nu -> has_increasing_set_continuity nu.
Proof.
move=> hX hd hn.
have hcompact := @real_power_compact_cutoff_laws R X
  (real_hausdorff_normalisation hp) p d nu hX
  (ltW (real_hausdorff_normalisation_positive hp)) (ltW hd) hn.
move=> A hinc.
exact: (@federer_2_10_22 R X
  (@real_power_compact_generator_cost R X (real_hausdorff_normalisation hp) p)
  (@real_power_compact_cost_nonnegative_degree R X (real_hausdorff_normalisation hp) p
    (real_hausdorff_normalisation_positive hp) hp) d nu A hX hd hcompact hinc).
Qed.

(** Source for [real_hausdorff_weighted_proper_equality]: direct
    real-degree Hausdorff application in 2.10.24,
    p. 188. The original all-nonempty-subset generator
    family is preserved. Bounded compactness replaces
    the finite-measure support-cover hypothesis, and
    infinite function and integral values are included. *)
Theorem real_hausdorff_weighted_proper_equality (R : realType) (X : metricType R) (p : R) (hp : (0<=p)%R)
    (f : X -> extended_real_line R) :
  metric_boundedly_compact X -> (forall x, 0<=f x) ->
  weighted_metric_limit (fun j : @nonempty_metric_sets R X=>val j)
    (fun j=>metric_real_diameter_cost (real_hausdorff_normalisation hp) p (val j)) (@real_hausdorff_measure R X p hp) f=
      measure_upper_integral (@real_hausdorff_measure R X p hp) (partial_function_total f).
Proof.
move=> hX hf.
pose J := @nonempty_metric_sets R X.
pose S (j : J) := (val j : set X).
pose c (j : J) := @metric_real_diameter_cost R X (real_hausdorff_normalisation hp) p (val j).
pose psi := @real_hausdorff_measure R X p hp.
pose L := @weighted_metric_limit R X J S c psi.
have hL := @weighted_metric_limit_specification R X J S c psi.
have hupper := @weighted_metric_limit_upper_integral_bound R X J S c psi L f
  (@real_hausdorff_measure_specification R X p hp) (fun j=>@metric_real_diameter_cost_ge0 R X (real_hausdorff_normalisation hp) p (val j) (ltW (real_hausdorff_normalisation_positive hp))) hL hf.
apply/eqP; rewrite eq_le hupper /=.
change (is_true (measure_upper_integral psi (partial_function_total f)<=L f)).
have hnon : 0<=L f := @weighted_metric_limit_nonnegative R X J S c psi L hL f.
case hval : (L f)=> [M| |] in hnon *; [|exact: leey|by []].
pose t n := ((n.+1%:R : R)^-1)%R.
pose A n := [set x | (t n)%:E<f x].
have ht n : (0<t n)%R by rewrite /t invr_gt0 ltr0n.
have hne (T : set X) (hT : T!=set0) : T<>set0 by move=> he; have [x hx] := hT; rewrite he in hx.
have hLM : L f<=M%:E by rewrite hval.
have hfinite n : psi (A n)< +oo.
  have hh := @weighted_limit_positive_level_bound R X [set T : set X | T!=set0]
    (@metric_real_diameter_cost R X (real_hausdorff_normalisation hp) p) psi (@hausdorff_generator_enlargement R X 1)
    (@real_hausdorff_enlargement_control R p) L f M (t n)
    (@real_hausdorff_generator_enlargement_specification R X (real_hausdorff_normalisation hp) p (ltW (real_hausdorff_normalisation_positive hp)) hp) hne
    (fun T _ hT=>@real_bounded_hausdorff_generator_cost_finite R X p hp T hT)
    (@real_hausdorff_measure_specification R X p hp) hL
    (fun d nu hd hn=>@real_hausdorff_finite_scale_continuity R X p hp d nu hX hd hn) hLM (ht n).
  exact: le_lt_trans hh (ltry _).
have hsupport : [set x | 0<f x] `<=` \bigcup_n A n.
  move=> x hx; have [N hN] := (@reciprocal_natural_order_limit R).2 (f x) hx.
  exists N=> //; exact: hN N (leqnn N).
have heq : L f=measure_upper_integral psi (partial_function_total f) :=
  @real_hausdorff_weighted_sigma_finite_equality R X p hp f A hf hfinite hsupport.
by rewrite -heq hval.
Qed.
