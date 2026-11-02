(** Federer (1969), 2.9.25, p. 169: after Fubini, the primitive of the
    summable inner integral is absolutely continuous. Apply 2.4.11, pp.
    85–86, to the union of the ordered intervals of 2.9.20(3), p. 165. No
    bounded-variation premise on the primitive is added. No relevant local
    Federer erratum entry. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology num_normedtype.
From Federer Require Import RealMetricBackground ExtendedRealOrderTopology
  PartialFunctionUP PartialAbsolutePartsGraph MeasureUP MeasureAlmostUP
  MeasureIntegralUP MeasureIntegralAbsolute MeasureIntegralAbsoluteContinuity
  MeasureIntegralUniqueness MeasureSubsetIntegral MeasureDensityUP MeasureDensity
  MeasureDensityNullSets SummableDensityMass SubsetAbsoluteIntegral
  LebesgueScalarMeasure RealSegmentIntegralDifference
  OrderedIntervalFamilyUP OrderedIntervalFamilyUnion MetricIntervalFamilyMassBound
  MetricCurveAbsoluteContinuityUP RealAbsoluteContinuityUP BorelRegularMeasureUP
  TopologicalBorel IntervalBumpFunctions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [summable_primitive_absolute_continuity]: direct primitive
    step of Federer 2.9.25, p. 169 The actual prefix integrals of any
    summable partial real density imply the printed finite interval-family
    condition of 2.9.20(3), p. 165. No representative or exceptional
    endpoint value is assumed. *)
Theorem summable_primitive_absolute_continuity (R : realType)
    (f : partial_function (real_line_metric R) (extended_real_line R))
    (g : R -> R) (a b : R) :
  is_measure_summable (@lebesgue_scalar_measure R) f ->
  (forall t : R, a<=t -> t<=b ->
    is_measure_subset_integral (@lebesgue_scalar_measure R) `[a,t] f (g t)%:E) ->
  is_absolutely_continuous_real_curve g a b.
Proof.
move=> hf hF; have hL := lebesgue_scalar_is_measure R.
have [I hI] := hf.
pose q := partial_extended_function_absolute_value f.
pose nu := measure_with_density (@lebesgue_scalar_measure R) q.
have hq := @measure_summable_absolute_value R (real_line_metric R)
  (@lebesgue_scalar_measure R) hL f hf.
have hn : is_measure nu := absolute_density_is_measure hL hI.1.
have hclosed u v : measure_measurable (@lebesgue_scalar_measure R) `[u,v].
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hL (lebesgue_scalar_borel_regular R)).
  exact: closed_borel_set (@segment_closed_real R u v).
have hopen u v : measure_measurable (@lebesgue_scalar_measure R) `]u,v[.
  apply: (@borel_regular_borel_measurable R [the topologicalType of real_line_metric R]
    (@lebesgue_scalar_measure R) hL (lebesgue_scalar_borel_regular R)).
  apply: open_borel_set; exact: interval_open.
have hnuopen u v : measure_measurable nu `]u,v[.
  exact (@absolute_density_measurable R (real_line_metric R)
    (@lebesgue_scalar_measure R) hL f `]u,v[ hI.1 (hopen u v)).
have hz x : nu [set x]=0%E.
  exact (@measure_density_null_set R (real_line_metric R) (@lebesgue_scalar_measure R)
    nu hL q [set x] (measure_with_density_laws _ q) (lebesgue_scalar_singleton x)).
have hinc u v : a<=u -> u<=v -> v<=b ->
    ((mdist ((g : R -> real_line_metric R) u) (g v))%:E<=nu `[u,v])%E.
  move=> hau huv hvb.
  have hU := hF u hau (le_trans huv hvb).
  have hV := hF v (le_trans hau huv) hvb.
  have hUV := @lebesgue_segment_integral_finite_difference R f a u v (g u) (g v) hau huv hU hV.
  have [J [hJ hbound]] := @subset_integral_absolute_bound R (real_line_metric R)
    (@lebesgue_scalar_measure R) hL `[u,v] f (g v-g u) hUV.
  have hnu := @summable_density_measurable_mass R (real_line_metric R)
    (@lebesgue_scalar_measure R) hL q `[u,v] hq (hclosed u v).
  have he := measure_integral_unique hJ hnu.
  by rewrite /mdist /= distrC he in hbound *.
move=> e he.
have [d [hd hsmall]] := @measure_integral_absolute_continuity R (real_line_metric R)
  (@lebesgue_scalar_measure R) hL f e hf he.
exists d; split=> // s hs hlen.
pose A := real_interval_family_open_union s.
have hA : measure_measurable (@lebesgue_scalar_measure R) A.
  exact: real_interval_family_open_union_measurable hL hopen.
have hAd : ((@lebesgue_scalar_measure R) A<=d%:E)%E.
  by rewrite /A (real_interval_family_open_union_length hs) lee_fin.
have [J [hJ hJe]] := hsmall A hA hAd.
have hnu := @summable_density_measurable_mass R (real_line_metric R)
  (@lebesgue_scalar_measure R) hL q A hq hA.
have hval : nu A=J%:E := measure_integral_unique hnu hJ.
have hb := @metric_interval_family_increment_mass_bound R [the metricType R of real_line_metric R]
  g nu a b s hn hnuopen hz hinc hs.
have heq : metric_interval_family_increment_sum (g : R -> real_line_metric R) s=
    real_interval_family_increment_sum g s.
  rewrite /metric_interval_family_increment_sum /real_interval_family_increment_sum.
  apply: eq_bigr=> uv _; exact: distrC.
rewrite heq -/A hval lee_fin in hb.
exact: le_trans hb (ltW hJe).
Qed.
