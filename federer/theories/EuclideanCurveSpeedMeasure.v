(** Federer (1969), 3.2.6, pp. 245–246: the actual
    speed gives a locally finite measure for an absolutely
    continuous curve. Use the proved norm-integral theorem
    of 2.9.22 and the sealed density operator of 2.4.10. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness NormMetric NormedCurveDerivativeUP NormedCurveDerivativeIntegrands
  LocallyAbsolutelyContinuousCurve EuclideanCurveDifferentiability
  NormedDerivativeVariationMeasure NormedVariationIntegralAbsoluteContinuity NormedCurveAbsoluteContinuityUP
  CurveArcLength CurveVariationUP StieltjesMonotone StieltjesImageMeasures
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialZeroExtensionLaws
  MeasureUP MeasureSplit PartialExtendedOrderLoci MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralBounds MeasureIntegralUniqueness
  MeasureSubsetIntegral MeasurableFunctionUP MeasurableGraphEquivalence
  MeasureDensityUP MeasureDensity MeasureDensityNullSets MeasureDensityTransfer
  ScalarLebesgueBallContext MeasureDerivationContext DensityBorelRegular BorelRegularMeasureUP
  LebesgueScalarMeasure RealMetricBackground ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_curve_speed]: the actual factor
    |f'| in Federer 3.2.6, p. 245. It is
    the existing partial norm derivative, without any default
    at a point where f' does not exist. *)
Definition euclidean_curve_speed (R:realType) n (f:R->R_n R n):=
  normed_curve_norm_derivative_integrand (inner_norm_real_norm (@euclidean_inner_productP R n)) f.

(** Source for [euclidean_curve_speed_measurable]: supporting
    measurability of |f'| for Federer 3.2.6, p. 245.
    Apply the norm variation measure representation of 2.9.22
    on the whole scalar line, then remove the vacuous cutoff. *)
Lemma euclidean_curve_speed_measurable (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)):
  is_locally_absolutely_continuous_curve f ->
  is_measure_measurable_function (@lebesgue_scalar_measure R) (euclidean_curve_speed f).
Proof.
move=>hAC.
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
have hBV:=locally_absolutely_continuous_curve_finite_variation hAC.
have hAE:=euclidean_absolute_continuous_derivative_almost hAC.
have hs (a b:R):(a<=b)%R -> (arc_length f a<=arc_length f b)%R:=
  @arc_length_monotone R [the metricType R of real_norm_metric_space hN] f hBV a b.
have hFin:=monotone_locally_finite_variation hs.
have [psip [psim hp]]:=induced_measure_pair_exists hFin.
have hLaws:=@normed_derivative_variation_measure_laws R (R_n R n)
  (inner_norm (@euclidean_inner_productP R n)) hN f psip psim hBV hAE hp.
have hSubset:=(hLaws.2.1 setT (measure_measurable_whole (lebesgue_scalar_is_measure R))).2.
apply:(@measurable_function_graph_equivalent R [the choiceType of real_line_metric R]
  (extended_real_line R) (@lebesgue_scalar_measure R) _ (euclidean_curve_speed f) _ hSubset.1).
by move=>x z; rewrite partial_zero_extension_whole_graph.
Qed.

(** Source for [euclidean_curve_speed_measure]: supporting
    measure with density |f'| in the use of 3.2.5
    in Federer 3.2.6, p. 246. Its defining operator
    is already opaque; no new chosen construction is exposed. *)
Definition euclidean_curve_speed_measure (R:realType) n (f:R->R_n R n):=
  measure_with_density (@lebesgue_scalar_measure R) (euclidean_curve_speed f).

(** Source for [euclidean_curve_speed_measure_laws]: the density
    specification of 2.4.10, p. 85, applied to the actual
    speed in Federer 3.2.6, p. 245. *)
Lemma euclidean_curve_speed_measure_laws (R:realType) n (f:R->R_n R n):
  is_measure_density (@lebesgue_scalar_measure R) (euclidean_curve_speed f) (euclidean_curve_speed_measure f).
Proof. exact:measure_with_density_laws. Qed.

(** Source for [euclidean_curve_speed_nonnegative_almost]:
    positivity of the norm factor |f'| in Federer 3.2.6,
    p. 245, with its proved conull actual domain. *)
Lemma euclidean_curve_speed_nonnegative_almost (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)):
  is_locally_absolutely_continuous_curve f ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    (PartialExtendedOrderLoci.partial_extended_nonnegative_locus (euclidean_curve_speed f)).
Proof.
move=>hAC.
apply:(@measure_almost_everywhere_mono R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) _ _ _
  (measurable_function_domain (euclidean_curve_speed_measurable hAC)))=>x [z hz].
exists z; split=>//; exact (normed_curve_norm_derivative_nonnegative hz).
Qed.

(** Source for [euclidean_curve_speed_measure_is_measure]: the
    measure assertion required for the speed factor in Federer
    3.2.6, p. 245, by the proved density measure laws. *)
Lemma euclidean_curve_speed_measure_is_measure (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)):
  is_locally_absolutely_continuous_curve f -> is_measure (euclidean_curve_speed_measure f).
Proof. move=>hAC; exact (measure_with_density_is_measure (lebesgue_scalar_is_measure R)
  (euclidean_curve_speed_nonnegative_almost hAC)). Qed.

(** Source for [euclidean_curve_speed_measure_borel_regular]:
    the Borel regular density measure used to localize the
    integral in Federer 3.2.6, pp. 245–246. This is
    proved from the existing Lebesgue class-M and density laws. *)
Lemma euclidean_curve_speed_measure_borel_regular (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)):
  is_locally_absolutely_continuous_curve f -> @is_borel_regular_measure R [the topologicalType of real_line_metric R] (euclidean_curve_speed_measure f).
Proof.
move=>hAC; exact (@density_is_borel_regular R [the metricType R of real_line_metric R]
  (@lebesgue_scalar_measure R) (euclidean_curve_speed_measure f) (euclidean_curve_speed f)
  (scalar_lebesgue_derivation_class R) (euclidean_curve_speed_measure_laws f)
  (euclidean_curve_speed_measurable hAC) (euclidean_curve_speed_nonnegative_almost hAC)).
Qed.

(** Source for [euclidean_curve_speed_measure_interval]: the
    identity between speed integral and interval length from
    2.9.22 and 2.10.13, used in Federer 3.2.6, p. 246.
    This assertion retains the actual norm-derivative integral. *)
Lemma euclidean_curve_speed_measure_interval (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)) a b:
  is_locally_absolutely_continuous_curve f -> (a<b)%R ->
  euclidean_curve_speed_measure f `[a,b]=curve_variation f a b.
Proof.
move=>hAC hab.
pose hN:=inner_norm_real_norm (@euclidean_inner_productP R n).
have hBV:=locally_absolutely_continuous_curve_finite_variation hAC.
have hAE:=euclidean_absolute_continuous_derivative_almost hAC.
have hIntegral:=(@normed_variation_integral_equality_absolute_continuity R (R_n R n)
  (inner_norm (@euclidean_inner_productP R n)) hN f a b hBV hAE hab).2 (hAC a b hab).
rewrite (euclidean_curve_speed_measure_laws f `[a,b]).
exact (@measure_upper_integral_unique R [the choiceType of real_line_metric R] (@lebesgue_scalar_measure R)
  _ _ _ (measure_upper_integral_specification _ _) hIntegral.2.1).
Qed.
