(** Federer (1969), 3.2.6, pp. 245–246: restrict
    the actual speed to the bounded measurable set A.
    The finite density measure has compact support in a
    containing scalar interval. Its selected operator is the
    already sealed density measure, not a new construction. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness
  RealMetricBackground ExtendedRealOrderTopology LocallyAbsolutelyContinuousCurve EuclideanCurveDifferentiability
  EuclideanCurveSpeedMeasure EuclideanCurveAreaFormula BoundedRealMetricInterval CurveArcLength CurveVariationUP
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialZeroExtensionLaws PartialExtendedOrderLoci
  MeasureUP MeasureBasic MeasureSplit MeasureRestriction MeasureAlmostUP MeasureAlmostBasic
  MeasurableFunctionUP MeasurableZeroExtension ZeroExtensionNonnegative
  MeasureDensityUP MeasureDensity MeasureDensityTransfer DensityBorelRegular ScalarLebesgueBallContext
  MeasureSubsetIntegral MeasureIntegralBounds MeasureBoundGraphEquivalence
  BorelRegularMeasureUP CoveringFamilyUP LebesgueScalarMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [euclidean_curve_restricted_speed]: the
    zero-extended subset integrand of |f'| on A in
    Federer 3.2.6, p. 245. Undefined derivatives
    inside A retain their original missing graph values. *)
Definition euclidean_curve_restricted_speed (R:realType) n (f:R->R_n R n)
    (A:set (real_line_metric R)):=partial_function_zero_extension (0:extended_real_line R) A (euclidean_curve_speed f).

(** Source for [euclidean_curve_restricted_speed_measure]:
    the speed measure restricted to A, supporting Federer
    3.2.6, pp. 245–246, via the opaque density operator. *)
Definition euclidean_curve_restricted_speed_measure (R:realType) n (f:R->R_n R n)
    (A:set (real_line_metric R)):=measure_with_density (@lebesgue_scalar_measure R) (euclidean_curve_restricted_speed f A).

(** Source for [euclidean_curve_restricted_speed_measure_laws]:
    abstract density specification for the restriction used in
    Federer 3.2.6, p. 245, by 2.4.10, p. 85. *)
Lemma euclidean_curve_restricted_speed_measure_laws (R:realType) n (f:R->R_n R n) A:
  is_measure_density (@lebesgue_scalar_measure R) (euclidean_curve_restricted_speed f A)
    (euclidean_curve_restricted_speed_measure f A).
Proof. exact:measure_with_density_laws. Qed.

(** Source for [euclidean_curve_restricted_speed_measureE]:
    supporting restriction identity in Federer 3.2.6,
    p. 245. It holds on arbitrary test sets by the
    exact intersection law for the two zero extensions. *)
Lemma euclidean_curve_restricted_speed_measureE (R:realType) n (f:R->R_n R n) A T:
  euclidean_curve_restricted_speed_measure f A T=euclidean_curve_speed_measure f (A `&` T).
Proof.
rewrite (euclidean_curve_restricted_speed_measure_laws f A T) (euclidean_curve_speed_measure_laws f (A `&` T)).
apply:measure_upper_integral_graph_equivalent=>x z.
by rewrite /euclidean_curve_restricted_speed partial_zero_extension_intersection_graph setIC.
Qed.

(** Source for [euclidean_curve_restricted_speed_measurable]:
    measurable restriction of the speed integrand in Federer
    3.2.6, p. 245; measurability is proved from A
    and the actual norm-derivative graph. *)
Lemma euclidean_curve_restricted_speed_measurable (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)) (A:set (real_line_metric R)):
  is_locally_absolutely_continuous_curve f -> measure_measurable (@lebesgue_scalar_measure R) A ->
  is_measure_measurable_function (@lebesgue_scalar_measure R) (euclidean_curve_restricted_speed f A).
Proof. move=>hAC hA; exact (@measurable_zero_extension R [the choiceType of real_line_metric R]
  (extended_real_line R) (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) 0 A
  (euclidean_curve_speed f) hA (euclidean_curve_speed_measurable hAC)). Qed.

(** Source for [euclidean_curve_restricted_speed_nonnegative]:
    norm positivity on the exact subset integrand in Federer
    3.2.6, p. 245, including zero outside A. *)
Lemma euclidean_curve_restricted_speed_nonnegative (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)) (A:set (real_line_metric R)):
  is_locally_absolutely_continuous_curve f ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    (partial_extended_nonnegative_locus (euclidean_curve_restricted_speed f A)).
Proof. move=>hAC; exact (zero_extension_nonnegative_almost (lebesgue_scalar_is_measure R)
  A (euclidean_curve_speed_nonnegative_almost hAC)). Qed.

(** Source for [euclidean_curve_restricted_speed_finite_almost]:
    the speed factor in Federer 3.2.6, p. 245,
    has finite nonnegative actual values almost everywhere.
    The conull derivative-existence theorem supplies them. *)
Lemma euclidean_curve_restricted_speed_finite_almost (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)) (A:set (real_line_metric R)):
  is_locally_absolutely_continuous_curve f ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x|exists r:R,(0<=r)%R /\ partial_function_graph (euclidean_curve_restricted_speed f A) x r%:E].
Proof.
move=>hAC; apply:(@measure_almost_everywhere_mono R [the choiceType of real_line_metric R]
  (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R) _ _ _
  (euclidean_absolute_continuous_derivative_almost hAC))=>x [v hv].
case:(pselect (A x))=>hx.
- exists (inner_norm (@euclidean_inner_productP R n) v); split; first exact:inner_norm_nonnegative.
  apply/partial_function_zero_extension_graph; left; split=>//; exists v; by split.
- exists 0%R; split; first exact:lexx.
  apply/partial_function_zero_extension_graph; right; by split.
Qed.

(** Source for [euclidean_curve_restricted_speed_is_measure]:
    actual measure law for the bounded-source speed in
    Federer 3.2.6, p. 245. *)
Lemma euclidean_curve_restricted_speed_is_measure (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)) (A:set (real_line_metric R)):
  is_locally_absolutely_continuous_curve f -> is_measure (euclidean_curve_restricted_speed_measure f A).
Proof. move=>hAC; exact (measure_with_density_is_measure (lebesgue_scalar_is_measure R)
  (euclidean_curve_restricted_speed_nonnegative A hAC)). Qed.

(** Source for [euclidean_curve_restricted_speed_borel_regular]:
    the Borel regular density needed for the completed-measure
    argument in Federer 3.2.6, pp. 245–246. *)
Lemma euclidean_curve_restricted_speed_borel_regular (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)) (A:set (real_line_metric R)):
  is_locally_absolutely_continuous_curve f -> measure_measurable (@lebesgue_scalar_measure R) A ->
  @is_borel_regular_measure R [the topologicalType of real_line_metric R]
    (euclidean_curve_restricted_speed_measure f A).
Proof.
move=>hAC hA; exact (@density_is_borel_regular R [the metricType R of real_line_metric R]
  (@lebesgue_scalar_measure R) (euclidean_curve_restricted_speed_measure f A)
  (euclidean_curve_restricted_speed f A) (scalar_lebesgue_derivation_class R)
  (euclidean_curve_restricted_speed_measure_laws f A)
  (euclidean_curve_restricted_speed_measurable hAC hA) (euclidean_curve_restricted_speed_nonnegative A hAC)).
Qed.

(** Source for [euclidean_curve_restricted_speed_finite_support]:
    localization of bounded A in Federer 3.2.6, p. 245.
    The restricted speed has finite total mass and vanishes
    off a nondegenerate compact interval containing A. *)
Lemma euclidean_curve_restricted_speed_finite_support (R:realType) n
    (f:R->inner_metric_space (@euclidean_inner_productP R n)) (A:set (real_line_metric R)):
  is_locally_absolutely_continuous_curve f -> metric_set_bounded A ->
  exists a b:R,(a<b)%R /\ A `<=` `[a,b] /\
    euclidean_curve_restricted_speed_measure f A setT< +oo /\
    euclidean_curve_restricted_speed_measure f A (~` `[a,b])=0.
Proof.
move=>hAC hBound; have [a [b [hab hAI]]]:=bounded_real_metric_interval_exists hBound.
exists a,b; split=>//; split=>//; split.
- rewrite euclidean_curve_restricted_speed_measureE setIT.
  apply:le_lt_trans (measure_mono (euclidean_curve_speed_measure_is_measure hAC) hAI) _.
  rewrite (euclidean_curve_speed_measure_interval hAC hab).
  exact (locally_absolutely_continuous_curve_finite_variation hAC (ltW hab)).
- rewrite euclidean_curve_restricted_speed_measureE.
  have he:A `&` (~` `[a,b])=set0.
    apply/seteqP; split; last by [].
    move=>x [hx hn]; exact (hn (hAI x hx)).
  rewrite he; exact:measure_empty (euclidean_curve_speed_measure_is_measure hAC).
Qed.
