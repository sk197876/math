(** Federer (1969), 2.10.24, p. 188: integer Hausdorff weighted-integral
    equality on boundedly compact metric spaces, without a
    sigma-finite-support assumption. At finite cutoffs the compact-generator
    reduction supplies actual continuity below from 2.10.22. The weak-level
    estimate then gives finite measures of positive levels, and the proved
    Hausdorff sigma-finite equality applies. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology PartialFunctionBasic MeasureIntegralBounds MetricDiameterUP MetricDiameter
  HausdorffLengthUP HausdorffMeasure HausdorffDiameterCost HausdorffPowerCostLaws
  CompactSetDistanceProfile CompactCostContinuityBelow LipschitzFunctionCompact IncreasingProjectionLoss
  MetricScaleEnvelopeUP MetricScaleEnvelope ClosedHausdorffEnlargementUP HausdorffGeneratorEnlargement
  HausdorffCompactCost HausdorffCompactScaleAgreement WeightedMetricLimit WeightedMetricLimitLaws
  WeightedLimitLevelBound WeightedUpperIntegralBound HausdorffWeightedSigmaFinite ReciprocalSequenceLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [bounded_hausdorff_generator_cost_finite]: supporting
    finite gauge on the eligible bounded generators of
    2.10.24, p. 188. Unbounded generators outside
    a finite cutoff may retain infinite cost. *)
Lemma bounded_hausdorff_generator_cost_finite (R : realType) (X : metricType R) (m : nat) (S : set X) :
  extended_metric_diameter S< +oo -> hausdorff_diameter_cost m S< +oo.
Proof.
move=> hf; have hn := metric_diameter_nonnegative (extended_metric_diameter_specification S).
have hfin : extended_metric_diameter S \is a fin_num by rewrite (ge0_fin_numE hn).
have he := fineK hfin.
rewrite /hausdorff_diameter_cost -he hausdorff_power_cost_finite; exact: ltry.
Qed.

(** Source for [hausdorff_finite_scale_continuity]: supporting
    actual continuity-below input for the Hausdorff
    application of 2.10.24, p. 188. It follows
    from exact compact-cover agreement at each positive
    finite cutoff and the checked theorem 2.10.22. *)
Theorem hausdorff_finite_scale_continuity (R : realType) (X : metricType R) (m : nat)
    (d : R) (nu : set X -> \bar R) :
  metric_boundedly_compact X -> (0<d)%R ->
  is_metric_scale_envelope (fun j : @nonempty_metric_sets R X=>val j)
    (fun j=>hausdorff_diameter_cost m (val j)) d%:E nu -> has_increasing_set_continuity nu.
Proof.
move=> hX hd hn.
pose cost := @hausdorff_compact_generator_cost R X m.
pose xi := metric_scale_envelope (fun C : compact_metric_set X=>val C) (fun C=>(cost C)%:E) d%:E.
have hxi := @metric_scale_envelope_specification R X (compact_metric_set X) (fun C=>val C) (fun C=>(cost C)%:E) d%:E.
have hecost : (fun C : compact_metric_set X=>hausdorff_diameter_cost m (val C))=(fun C=>(cost C)%:E).
  apply: funext=> C; exact: hausdorff_compact_generator_cost_value.
have hxiorig : is_metric_scale_envelope (fun C : compact_metric_set X=>val C)
    (fun C=>hausdorff_diameter_cost m (val C)) d%:E xi by rewrite hecost.
have heq : nu=xi.
  apply: funext=> A; exact: (@hausdorff_compact_scale_agreement R X m d nu xi hX (ltW hd) hn hxiorig A).
move=> A hinc; rewrite heq.
exact: (@federer_2_10_22 R X cost (@hausdorff_compact_generator_cost_laws R X m) d xi A hX hd hxi hinc).
Qed.

(** Source for [hausdorff_weighted_proper_equality]: direct
    integer-degree Hausdorff application in 2.10.24,
    p. 188. The original all-nonempty-subset generator
    family is preserved. Bounded compactness replaces
    the finite-measure support-cover hypothesis, and
    infinite function and integral values are included. *)
Theorem hausdorff_weighted_proper_equality (R : realType) (X : metricType R) (m : nat)
    (f : X -> extended_real_line R) :
  metric_boundedly_compact X -> (forall x, 0<=f x) ->
  weighted_metric_limit (fun j : @nonempty_metric_sets R X=>val j)
    (fun j=>hausdorff_diameter_cost m (val j)) (@hausdorff_measure R X m) f=
      measure_upper_integral (@hausdorff_measure R X m) (partial_function_total f).
Proof.
move=> hX hf.
pose J := @nonempty_metric_sets R X.
pose S (j : J) := (val j : set X).
pose c (j : J) := @hausdorff_diameter_cost R X m (val j).
pose psi := @hausdorff_measure R X m.
pose L := @weighted_metric_limit R X J S c psi.
have hL := @weighted_metric_limit_specification R X J S c psi.
have hupper := @weighted_metric_limit_upper_integral_bound R X J S c psi L f
  (@hausdorff_measure_specification R X m) (fun j=>@hausdorff_diameter_cost_nonnegative R X m (val j)) hL hf.
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
    (@hausdorff_diameter_cost R X m) psi (@hausdorff_generator_enlargement R X m)
    (closed_hausdorff_enlargement_control R m) L f M (t n)
    (@hausdorff_generator_enlargement_laws R X m) hne
    (fun T _ hT=>@bounded_hausdorff_generator_cost_finite R X m T hT)
    (@hausdorff_measure_specification R X m) hL
    (fun d nu hd hn=>@hausdorff_finite_scale_continuity R X m d nu hX hd hn) hLM (ht n).
  exact: le_lt_trans hh (ltry _).
have hsupport : [set x | 0<f x] `<=` \bigcup_n A n.
  move=> x hx; have [N hN] := (@reciprocal_natural_order_limit R).2 (f x) hx.
  exists N=> //; exact: hN N (leqnn N).
have heq : L f=measure_upper_integral psi (partial_function_total f) :=
  @hausdorff_weighted_sigma_finite_equality R X m f A hf hfinite hsupport.
by rewrite -heq hval.
Qed.
